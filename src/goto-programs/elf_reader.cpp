/*******************************************************************\

Module: Read ELF

Author:

\*******************************************************************/

#include "elf_reader.h"

/*******************************************************************\

Function: elf_readert::elf_readert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

elf_readert::elf_readert(std::istream &_in):in(_in)
{
  // read header
  in.read((char *)&elf_header, sizeof(elf_header));

  if(!in)
    throw "failed to read ELF header";

  if(elf_header.e_ident[0]!=0x7f ||
     elf_header.e_ident[1]!='E' ||
     elf_header.e_ident[2]!='L' ||
     elf_header.e_ident[3]!='F')
   throw "ELF header malformed (magic)";
  
  char ei_data=elf_header.e_ident[5];
  
  bool little_endian;
  
  if(ei_data==1)
    little_endian=true;
  else if(ei_data==2)
    little_endian=false;
  else
    throw "ELF header malformed (EI_DATA)";
  
  // get offset for section header
  if(elf_header.e_shoff==0)
    throw "ELF without section header";
  
  section_header_table.resize(elf_header.e_shnum);

  // iterate over these
  for(unsigned i=0; i<section_header_table.size(); i++)
  {
    // go to right place
    in.seekg(elf_header.e_shoff+i*elf_header.e_shentsize);

    // read section header
    in.read((char *)&section_header_table[i], sizeof(Elf32_Shdr));
  }
  
  // string table
  unsigned string_table_nr=elf_header.e_shstrndx;
  if(string_table_nr>=section_header_table.size())
    throw "ELF without string table";

  string_table_offset=section_header_table[string_table_nr].sh_offset;
}

/*******************************************************************\

Function: elf_readert::get_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string elf_readert::get_string(unsigned index)
{
  in.seekg(string_table_offset+index);

  std::string result;

  while(in)
  {
    char ch;
    in.read(&ch, 1);
    if(ch==0) break;
    result+=ch;
  }
  
  return result;
}
