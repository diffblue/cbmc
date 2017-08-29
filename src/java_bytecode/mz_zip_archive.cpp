/*******************************************************************\

Module: mz_zip library wrapper

Author: Diffblue Ltd

\*******************************************************************/

#include "mz_zip_archive.h"
#include <stdexcept>
#include <string>
#include <vector>
#include <algorithm>
#define _LARGEFILE64_SOURCE 1
#include <miniz/miniz.h>

// Original struct is an anonymous struct with a typedef, This is
// required to remove internals from the header file
class mz_zip_archive_statet final:public mz_zip_archive
{
public:
  explicit mz_zip_archive_statet(const std::string &filename):
    mz_zip_archive({ })
  {
    if(MZ_TRUE!=mz_zip_reader_init_file(this, filename.data(), 0))
      throw std::runtime_error("MZT: Could not load a file: "+filename);
  }
  mz_zip_archive_statet(const mz_zip_archive_statet &)=delete;
  mz_zip_archive_statet(mz_zip_archive_statet &&)=delete;
  mz_zip_archive_statet &operator=(const mz_zip_archive_statet &)=delete;
  mz_zip_archive_statet &operator=(mz_zip_archive_statet &&)=delete;
  ~mz_zip_archive_statet()
  {
    mz_zip_reader_end(this);
  }
};

static_assert(sizeof(mz_uint)<=sizeof(size_t),
              "size_t cannot store mz_zip file ids, choose a larger type");

mz_zip_archivet::mz_zip_archivet(const std::string &filename):
  m_state(new mz_zip_archive_statet(filename)) { }

// VS Compatibility
mz_zip_archivet::mz_zip_archivet(mz_zip_archivet &&other):
  m_state(std::move(other.m_state)) { }

// Has to be defined here because header is incomplete
mz_zip_archivet::~mz_zip_archivet()=default;

// VS Compatibility
mz_zip_archivet &mz_zip_archivet::operator=(mz_zip_archivet &&other)
{
  m_state=std::move(other.m_state);
  return *this;
}

size_t mz_zip_archivet::get_num_files()
{
  return mz_zip_reader_get_num_files(m_state.get());
}

std::string mz_zip_archivet::get_filename(const size_t index)
{
  const auto id=static_cast<mz_uint>(index);
  std::vector<char> buffer;
  buffer.resize(mz_zip_reader_get_filename(m_state.get(), id, nullptr, 0));
  mz_zip_reader_get_filename(m_state.get(), id, buffer.data(), buffer.size());
  // Buffer may contain junk returned after \0
  const auto null_char_it=std::find(buffer.cbegin(), buffer.cend(), '\0');
  return { buffer.cbegin(), null_char_it };
}

std::string mz_zip_archivet::extract(const size_t index)
{
  const auto id=static_cast<mz_uint>(index);
  mz_zip_archive_file_stat file_stat={ };
  const mz_bool stat_ok=mz_zip_reader_file_stat(m_state.get(), id, &file_stat);
  if(stat_ok==MZ_TRUE)
  {
    std::vector<char> buffer(file_stat.m_uncomp_size);
    const mz_bool read_ok=mz_zip_reader_extract_to_mem(
      m_state.get(), id, buffer.data(), buffer.size(), 0);
    if(read_ok==MZ_TRUE)
      return { buffer.cbegin(), buffer.cend() };
  }
  throw std::runtime_error("Could not extract the file");
}

