#include <filesystem>
#include <fstream>
#include <iostream>
#include <string>

#include "AsyncIo.h"
#include "Runtime.h"
#include "Type.h"
#include "Util.h"
#include "boilerplate.h"
#include "filesystem.h"
#include "galois/Timer.h"
#include "llvm/Support/CommandLine.h"

namespace cll = llvm::cl;
#pragma pack(push, 1)
struct MetaHeader {
  uint8_t vsize, esize, wsize;
  uint32_t num_nodes;
  uint64_t num_edges;
};
#pragma pack(pop)

static cll::opt<int> numDisks("numDisks", cll::desc("Number of disks (default value 1)"),
                              cll::init(1));

static cll::opt<bool> weighted("weighted",
                               cll::desc("Flag for weighted graph (default value: false)"),
                               cll::init(false));

static cll::opt<std::string> inputFilename(cll::Positional, cll::desc("<input file>"),
                                           cll::Required);
static cll::opt<std::string> outFilename(cll::Positional, cll::desc("<output file>"),
                                         cll::Required);

using namespace blaze;

std::string get_index_file_name(const std::string& input) { return input + "/index"; }

void get_adj_file_names(const std::string& input, int num_disks,
                        std::vector<std::string>& out_files) {
  for (int i = 0; i < num_disks; i++) {
    out_files.push_back(input + "/adj." + std::to_string(num_disks) + "." + std::to_string(i));
  }
}

struct graph_header read_meta(const std::string& meta_path) {
  if (!file_exists(meta_path)) {
    throw std::runtime_error("Meta file does not exist");
  }
  if (std::filesystem::file_size(meta_path) != sizeof(MetaHeader)) {
    throw std::runtime_error("Meta file size is not correct");
  }
  int meta_fd = open(meta_path.c_str(), O_RDONLY);
  assert(meta_fd > 0);
  MetaHeader meta_header;
  auto ret = read(meta_fd, &meta_header, sizeof(meta_header));
  assert(ret == sizeof(meta_header));
  close(meta_fd);

  assert(meta_header.vsize == 4);
  assert(meta_header.esize == 8);
  struct graph_header header;
  header.unused = 0;
  header.size_of_edge = meta_header.vsize + meta_header.wsize;
  header.num_nodes = meta_header.num_nodes;
  header.num_edges = meta_header.num_edges;
  printf("header.size_of_edge: %lu\n", header.size_of_edge);
  printf("header.num_nodes: %lu\n", header.num_nodes);
  printf("header.num_edges: %lu\n", header.num_edges);
  return header;
}

void write_index_file(const std::string& input, std::string& out) {
  printf("write_index_file: input: %s\n", input.c_str());
  printf("write_index_file: out: %s\n", out.c_str());

  struct graph_header header = read_meta(input + "/meta");
  uint64_t index_file_size = sizeof(header) + sizeof(uint64_t) * header.num_nodes;
  // calculate space after compaction
  size_t num_offsets = ((header.num_nodes - 1) / 16) + 1;
  size_t len_header = sizeof(header) + num_offsets * sizeof(uint64_t);
  size_t len_header_aligned = ALIGN_UPTO(len_header, CACHE_LINE);

  size_t new_len = len_header_aligned + num_offsets * CACHE_LINE;

  printf("# nodes: %lu\n", header.num_nodes);
  printf("[original]\n");
  printf("  index size  : %lu\n", index_file_size);
  printf("\n");
  printf("[compact]\n");
  printf("  header size : %lu\n", len_header_aligned);
  printf("    header size  : %lu\n", sizeof(header));
  printf("    offset size  : %lu\n", num_offsets * sizeof(uint64_t));
  printf("    before align : %lu\n", len_header);
  printf("+ degree size : %lu\n", num_offsets * CACHE_LINE);
  printf("= index size  : %lu\n", new_len);

  std::string idx_path = input + "/offset";
  auto [base, len] = map_file(idx_path);
  char* new_base = create_and_map_file(out, new_len);

  uint64_t* index = (uint64_t*)(base) + 1;
  uint32_t degree;
  uint64_t offset;

  uint64_t* np = (uint64_t*)new_base;
  *np++ = 0;
  *np++ = 0;
  *np++ = header.num_nodes;
  *np++ = header.num_edges;

  uint64_t* new_index = (uint64_t*)np;
  uint32_t* degrees = (uint32_t*)(new_base + len_header_aligned);

  for (uint64_t node = 0; node < header.num_nodes; node++) {
    if (node == 0) {
      degree = index[node];
      offset = 0;

    } else {
      degree = index[node] - index[node - 1];
      offset = index[node - 1];
    }

    if (node % 16 == 0) {
      new_index[node / 16] = offset;
    }
    degrees[node] = degree;
  }

  munmap(base, len);

  msync(new_base, new_len, MS_SYNC);
  munmap(new_base, new_len);
}

void write_adj_files(const std::string& input, std::vector<std::string>& out_files) {
  printf("write_adj_files: out_files size: %lu\n", out_files.size());
  printf("write_adj_files: input: %s\n", input.c_str());
  printf("write_adj_files: out_files[0]: %s\n", out_files[0].c_str());
  struct graph_header header = read_meta(input + "/meta");
  std::string adj_path = input + "/data";
  auto [adj_base, adj_len] = map_file(adj_path);

  int num_disks = out_files.size();
  uint64_t tuple_size = sizeof(VID);
  if (weighted) tuple_size += sizeof(EDGEDATA);
  uint64_t total_edge_bytes = header.num_edges * tuple_size;
  assert(adj_len == total_edge_bytes);
  uint64_t total_num_pages = (total_edge_bytes - 1) / PAGE_SIZE + 1;
  uint64_t num_pages_per_disk = total_num_pages / num_disks;  // FIXME may not be equal

  int fd[num_disks];
  for (int i = 0; i < num_disks; i++) {
    fd[i] = open(out_files[i].c_str(), O_WRONLY | O_CREAT | O_TRUNC, 0644);
  }

  char* buf = adj_base;
  const char* buf_end = buf + total_edge_bytes;

  uint64_t page_cnt = 0;
  while (buf < buf_end) {
    size_t len = PAGE_SIZE;
    if (buf + len > buf_end) len = buf_end - buf;
    write(fd[page_cnt % num_disks], buf, len);
    if (len < PAGE_SIZE) {
      char tmp[PAGE_SIZE - len];
      write(fd[page_cnt % num_disks], tmp, PAGE_SIZE - len);
    }
    buf += PAGE_SIZE;
    page_cnt++;
  }

  for (int i = 0; i < num_disks; i++) {
    close(fd[i]);
  }

  munmap(adj_base, adj_len);
}

void convert(const std::string& input, const std::string& out, int num_disks) {
  // write index file
  auto index_file_name = get_index_file_name(out);
  write_index_file(input, index_file_name);

  // write adj files
  std::vector<std::string> adj_file_names;
  get_adj_file_names(out, num_disks, adj_file_names);
  write_adj_files(input, adj_file_names);
}

int main(int argc, char** argv) {
  AgileStart(argc, argv);
  Runtime runtime(numComputeThreads, numIoThreads, ioBufferSize * MB);

  galois::StatTimer timer("Time", "CONVERT");
  timer.start();
  if (!std::filesystem::exists(outFilename.c_str())) {
    std::filesystem::create_directories(outFilename.c_str());
  }
  convert(inputFilename, outFilename, numDisks);

  timer.stop();

  return 0;
}
