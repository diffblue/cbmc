/*******************************************************************\
 
Module: XML-irep conversions with hashing
 
Author: CM Wintersteiger
 
Date: July 2006
 
\*******************************************************************/

#ifndef XML_IREP_HASHING_H_
#define XML_IREP_HASHING_H_

#include <xml.h>
#include <irep.h>
#include <hash_cont.h>

class xml_irep_convertt {
  private:
   
    struct ul_hash
    {
      unsigned short operator()(const unsigned long l) const 
      { 
        return (l & 0xFFFF); 
      }
    };
    struct ul_eq
    {
      bool operator()(const unsigned long l, const unsigned long r) const 
      {
        return (l==r);
      }
    };
    struct irep_full_hash
    {
      size_t operator()(const irept &i) const 
      { 
        return i.full_hash(); 
      }
    };
    struct irep_content_eq
    {
      bool operator()(const irept &l, const irept &r) const 
      {
        return full_eq(l,r);
      }
    };
    
  public:    
    class ireps_containert {
      public:
        typedef hash_map_cont<unsigned long, irept, ul_hash, ul_eq> id_containert;
        id_containert id_container;
        typedef hash_map_cont<irept, unsigned long, irep_full_hash, irep_content_eq> content_containert;
        content_containert content_container;
        typedef std::map<unsigned, unsigned> id_replace_mapt;
        id_replace_mapt id_replace_map;        
        
        void clear( void ) { 
          id_container.clear(); 
          content_container.clear();
          id_replace_map.clear();
        }        
    };
    
    xml_irep_convertt(ireps_containert& ic) : ireps_container(ic) {};
    
    unsigned long insert(unsigned long, const irept&);
    unsigned long insert(const std::string&, const irept&);
    
    void convert(const irept &irep, xmlt &xml);      
    void convert(const xmlt &xml, irept &irep);
    void reference_convert(const irept &irep, xmlt &xml);
    void resolve_references( const irept &cur );
    
    void convert_map(xmlt &xml);
    void output_map(std::ostream &out, unsigned indent);
      
    void clear( void ) { ireps_container.clear(); }
  private:
    ireps_containert& ireps_container;    
    
    ireps_containert::id_containert::const_iterator 
      find_irep_by_id(const unsigned int);
    ireps_containert::content_containert::const_iterator 
      find_irep_by_content(const irept &irep);
    
    std::string long_to_string(const unsigned long);
    unsigned long string_to_long(const std::string &);
        
    unsigned long add_with_childs(const irept&);    
};

#endif /*XML_IREP_HASHING_H_*/
