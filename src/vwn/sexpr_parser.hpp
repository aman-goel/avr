/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


#ifndef sexpr_parser_hpp
#define sexpr_parser_hpp

#include <string> 
#include <cassert>
#include <iterator>
#include <vector>

namespace eufabs {
  enum class elt_ty { VALUE, LIST };
  enum class atom_ty { BASIC, SQUOTE, DQUOTE, BINARY };

  class sexpr;

  class sexpr {
    friend class sexpr_parser;

    void *_sexpr;
    
    public:
    sexpr(); // null
    sexpr(void *s);

    /* Frees the underlying sexpr and sets this handle to null */
    void destroy();

    /* True if sexpr is non-null, false otherwise */
    explicit operator bool() const;
    bool operator==(const sexpr& other) const;
    bool operator!=(const sexpr& other) const;

    elt_ty getTy() const;
    bool isList() const { return getTy() == elt_ty::LIST; }
    bool isValue() const { return getTy() == elt_ty::VALUE; }
    atom_ty getAtomTy() const;
    /* Pointer to raw data */
    const char *const getVal() const;
    /* Copy string values, ie, BASIC, SQUOTE, DQUOTE */
    std::string copyVal() const;
    /* If type is LIST */
    sexpr getList() const;
    /* If inside a LIST; will be null if no more elements */
    sexpr getNext() const;

    std::string asString() const;
  
    class iterator : public std::iterator<
                     std::forward_iterator_tag, // category
                     const sexpr,                     // value_type
                     long,                      // difference_type
                     const sexpr*,                    // pointer
                     const sexpr> {                   // reference
      void *_sexpr;
      
    public:
      explicit iterator(void *s = nullptr) : _sexpr(s) {}
      iterator operator++(int) { sexpr s(_sexpr); _sexpr = s.getNext()._sexpr; return iterator(s._sexpr); }
      const sexpr operator*() { return sexpr(_sexpr); }
      bool operator==(iterator rhs) { return _sexpr == rhs._sexpr; }
      bool operator!=(iterator rhs) { return _sexpr != rhs._sexpr; }
    };

    iterator begin() const { auto list = getList(); return iterator(list._sexpr); }
    iterator end() const { return iterator(); }

  };
    


  class sexpr_parser {
    void *iowrap;
    std::vector<sexpr> exprs;

    public:
    /* Create parser backed by filename */
    sexpr_parser(const std::string& filename);
    ~sexpr_parser();

    /* parses and returns th next sexpr */
    sexpr getNextSexpr();




  class iterator {
  private:
    sexpr_parser& parser;
    std::vector<sexpr>::iterator curr;
    
  public:
    typedef iterator self_type;
    typedef sexpr value_type;
    typedef const sexpr& reference;
    typedef sexpr *pointer;
    typedef std::forward_iterator_tag iterator_category;
    typedef int difference_type;
    iterator(sexpr_parser& p, std::vector<sexpr>::iterator c) : parser(p), curr(c) {}
    inline self_type operator++(int) { iterator ret(*this); ++curr; return ret; }
    //inline self_type operator++(int) { self_type it(c, i); ++*this; return it; }
    inline reference operator*() { return *curr; }
    bool operator==(const self_type& rhs) { return &parser == &rhs.parser && curr == rhs.curr; }
    bool operator!=(const self_type& rhs) { return &parser != &rhs.parser || curr != rhs.curr; }
  };

  iterator begin();
  iterator end();
  };
}

#endif
