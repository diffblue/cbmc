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

  mz_zip_archive_statet(const void *data, size_t size):
    mz_zip_archive({ })
  {
    if(MZ_TRUE!=mz_zip_reader_init_mem(this, data, size, 0))
      throw std::runtime_error("MZT: Could not load data from memory");
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

mz_zip_archivet::mz_zip_archivet(const void *data, size_t size):
  m_state(new mz_zip_archive_statet(data, size)) { }

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
  const auto id = static_cast<mz_uint>(index);
  mz_uint name_size = mz_zip_reader_get_filename(m_state.get(), id, nullptr, 0);
  if(name_size == 0)
    return {}; // Failure
  // It is valid to directly write to a string's buffer (see C++11 standard,
  // basic_string general requirements [string.require], 21.4.1.5)
  std::string buffer(name_size, '\0');
  mz_zip_reader_get_filename(m_state.get(), id, &buffer[0], buffer.size());
  // Buffer contains trailing \0
  buffer.resize(name_size - 1);
  return buffer;
}

std::string mz_zip_archivet::extract(const size_t index)
{
  const auto id=static_cast<mz_uint>(index);
  mz_zip_archive_file_stat file_stat={ };
  const mz_bool stat_ok=mz_zip_reader_file_stat(m_state.get(), id, &file_stat);
  if(stat_ok==MZ_TRUE)
  {
    // It is valid to directly write to a string's buffer (see C++11 standard,
    // basic_string general requirements [string.require], 21.4.1.5)
    std::string buffer(file_stat.m_uncomp_size, '\0');
    const mz_bool read_ok = mz_zip_reader_extract_to_mem(
      m_state.get(), id, &buffer[0], buffer.size(), 0);
    if(read_ok == MZ_TRUE)
      return buffer;
  }
  throw std::runtime_error("Could not extract the file");
}

void mz_zip_archivet::extract_to_file(
  const size_t index,
  const std::string &path)
{
  const auto id = static_cast<mz_uint>(index);
  if(
    mz_zip_reader_extract_to_file(m_state.get(), id, path.c_str(), 0) !=
    MZ_TRUE)
  {
    throw std::runtime_error("Could not extract the file");
  }
}
