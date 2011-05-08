/* STL-conforming "sorted vector" container
 *
 * (C) 2002 Martin Holzherr (holzherr@infobrain.com). All rights reserved.
 *
 * Permission is granted to use, distribute and modify this code provided that:
 *   · this copyright notice appears,
 *   · 
 * The author welcomes any suggestions on the code or reportings of actual
 * use of the code. Please send your comments to holzherr@infobrain.com.
 *
 * The author makes NO WARRANTY or representation, either express or implied,
 * with respect to this code, its quality, accuracy, merchantability, or
 * fitness for a particular purpose.  This software is provided "AS IS", and
 * you, its user, assume the entire risk as to its quality and accuracy.
 *
 * Created:			November 19th, 2002
 * Last modified:	November 27th, 2002 
						(changed namespace from std to codeproject;
						uses template member functions for MSCVER>=1300)
								
 */

#ifndef SORTED_VECTOR_
#define SORTED_VECTOR_
#define VERSION_SORTED_VECTOR_ 0x00010010

#include <algorithm>
#include <vector>
#include <utility>
#include <functional>

//#pragma pack(push,8)
//#pragma warning(push,3)

template<
  class K,
  bool bNoDuplicates= false,
  class Pr = std::less<K>,
  class A = std::allocator<K> >
class sorted_vector
{
public:
  typedef sorted_vector<K,bNoDuplicates,Pr,A> Myt_;
  typedef typename std::vector<K, A> Cont;
  typedef typename Cont::allocator_type allocator_type;
  typedef typename Cont::size_type size_type;
  typedef typename Cont::difference_type difference_type;
  typedef typename Cont::reference reference;
  typedef typename Cont::const_reference const_reference;
  typedef typename Cont::value_type value_type;
  typedef K key_type;
  typedef typename Cont::iterator iterator;
  typedef typename Cont::const_iterator const_iterator;
  typedef Pr key_compare;
  typedef Pr value_compare;

  typedef typename Cont::const_reverse_iterator const_reverse_iterator;
  typedef typename Cont::reverse_iterator reverse_iterator;

  typedef std::pair<iterator, iterator> Pairii_;
  typedef std::pair<const_iterator, const_iterator> Paircc_;

  typedef std::pair<iterator, bool> Pairib_;
	explicit sorted_vector(const Pr& pred = Pr(),const A& al = A())
    :key_compare_(pred),vec_(al){}

#if (_MSC_VER >= 1300)
	template<class It>
	sorted_vector(It first, It beyond, 
					const Pr& pred = Pr(),const A& al = A())
		:key_compare_(pred),vec_(first,beyond,al)
        {stable_sort();}
#else
    sorted_vector(const_iterator first, const_iterator beyond, 
					const Pr& pred = Pr(),const A& al = A())
        :key_compare_(pred),vec_(first,beyond,al)
        {stable_sort();}
#endif
	sorted_vector(const Myt_& x)
		: key_compare_(x.key_compare_),vec_(x.vec_)
        {}
    ~sorted_vector()                {}
    Myt_& operator=(const Myt_& x) {vec_.operator=(x.vec_);
                                     key_compare_= x.key_compare_;
                                     return *this;}
    Myt_& operator=(const Cont& x){vec_.operator=(x);
                                    sort();return *this;}
		
	void				reserve(size_type n)	{vec_.reserve(n);}
	iterator			begin()					{return vec_.begin(); }
	const_iterator		begin() const			{return vec_.begin(); }
    iterator			end()					{return vec_.end();}
    const_iterator		end() const				{return vec_.end();}
    reverse_iterator	rbegin()				{return vec_.rbegin();}
    const_reverse_iterator rbegin() const   
												{return vec_.rbegin();}

    reverse_iterator rend()						{return vec_.rend();}
    const_reverse_iterator rend() const     
												{return vec_.rend();}


    size_type size() const						{return vec_.size();}
    size_type max_size() const					{return vec_.max_size();}
    bool empty() const							{return vec_.empty();}
    A get_allocator() const						{return vec_.get_allocator();}
    const_reference at(size_type p) const		{return vec_.at(p);}
    reference at(size_type p)					{return vec_.at(p);}
	const_reference operator[](size_type p) const
												{return vec_.operator[](p);}
		
	reference operator[](size_type p)			{return vec_.operator[](p);}
    reference front()							{return vec_.front();}
	const_reference front() const				{return vec_.front();}
    reference back()							{return vec_.back();}
    const_reference back() const				{return vec_.back();}
    void pop_back()								{vec_.pop_back();}

    void assign(const_iterator first, const_iterator beyond)					
												{vec_.assign(first,beyond);}
	void assign(size_type n, const K& x = K())
												{vec_.assign(n,x);}
/*insert members*/
   Pairib_ insert(const value_type& x)
		{
            if(bNoDuplicates){
                iterator p= lower_bound(x);
                if(p==end()||key_compare_(x,*p)){
                    return Pairib_(InsertImpl_(p,x),true);
                }else{
                    return Pairib_(p,false);
                }
            }else{
                iterator p= upper_bound(x);
                return Pairib_(InsertImpl_(p,x),true);
            }
        }
   iterator insert(iterator it, const value_type& x)//it is the hint
        {
           if(it!=end() ){
               if(bNoDuplicates){
                   if(key_compare_(*it,x)){
                       if((it+1)==end()||KeyCompare_Gt_(*(it+1),x)){//use hint
                            return InsertImpl_(it+1,x);
                       }else if(KeyCompare_Geq_(*(it+1),x)){
                           return end();
                       }
                    }
               }else{
                   if(	KeyCompare_Leq_(*it,x)
					   &&((it+1)==end()||KeyCompare_Geq_(*(it+1),x))){
                       return InsertImpl_(it+1,x);
                   }
               }
           }
           return insert(x).first;
        }
#if (_MSC_VER >= 1300)
  template<class It>
	void insert(It first, It beyond)
    {
        size_type n= std::distance(first,beyond);
        reserve(size()+n);
        for( ;first!=beyond;++first){
            insert(*first);
        }
    }
#else
   void insert(const_iterator first, const_iterator beyond)
        {
            size_type n= std::distance(first,beyond);
            reserve(size()+n);
            for( ;first!=beyond;++first){
                insert(*first);
            }
        }
#endif
    iterator erase(iterator p)          {return vec_.erase(p);}
	iterator erase(iterator first, iterator beyond)
                                        {return vec_.erase(first,beyond);}
    size_type erase(const K& key)     
        {
            Pairii_ begEnd= equal_range(key);
            size_type n= std::distance(begEnd.first,begEnd.second);
            erase(begEnd.first,begEnd.second);
            return n;
        }
    void clear()                        {return vec_.clear();}
		
    bool Eq_(const Myt_& x) const      
		{return (size() == x.size()
		&& std::equal(begin(), end(), x.begin())); }
	bool Lt_(const Myt_& x) const
        {return (std::lexicographical_compare(begin(), end(),
										x.begin(), x.end()));}
	void swap(Myt_& x)
        {vec_.swap(x.vec_);std::swap(key_compare_,x.key_compare_);}
        
	friend void swap(Myt_& x, Myt_& Y_)
		{x.swap(Y_); }

	key_compare key_comp() const			{return key_compare_; }
    value_compare value_comp() const		{return (key_comp()); }
	iterator find(const K& k)
		{	iterator p = lower_bound(k);
			return (p==end()||key_compare_(k, *p))? end():p;
		}
	const_iterator find(const K& k) const
		{const_iterator p = lower_bound(k);
        return (p==end()||key_compare_(k,*p))?end():p;}
	size_type count(const K& k) const
		{Paircc_ Ans_ = equal_range(k);
        size_type n = std::distance(Ans_.first, Ans_.second);
        return (n); }
	iterator lower_bound(const K& k)
        {return std::lower_bound(begin(), end(), k, key_compare_); }
	const_iterator lower_bound(const K& k) const
        {return std::lower_bound(begin(), end(), k, key_compare_); }
	iterator upper_bound(const K& k)
		{return std::upper_bound(begin(), end(), k, key_compare_); }
	const_iterator upper_bound(const K& k) const
		{return std::upper_bound(begin(), end(), k, key_compare_); }
	Pairii_ equal_range(const K& k)
        {return std::equal_range(begin(), end(), k, key_compare_); }
	Paircc_ equal_range(const K& k) const
		{return std::equal_range(begin(), end(), k, key_compare_); }

/*functions for use with direct std::vector-access*/
    Cont& get_container()
        {return vec_;}
    void sort()//restore sorted order after low level access 
        {   std::sort(vec_.begin(),vec_.end(),key_compare_);
            if( bNoDuplicates ){
                vec_.erase(Unique_(),vec_.end());
            }
        }
    void stable_sort()//restore sorted order after low level access 
        {   std::stable_sort(vec_.begin(),vec_.end(),key_compare_);
            if( bNoDuplicates ){
                erase(Unique_(),end());
            }
        }   

protected:
  iterator Unique_()
  {
    iterator front_= vec_.begin(),out_= vec_.end(),end_=vec_.end();
            bool bCopy_= false;
            for(iterator prev_; (prev_=front_)!=end_ && ++front_!=end_; ){
                if( key_compare_(*prev_,*front_)){
                    if(bCopy_){
                        *out_= *front_;
                        out_++;
                    }
                }else{
                    if(!bCopy_){out_=front_;bCopy_=true;}
                }
            }
            return out_;
        }
    iterator InsertImpl_(iterator p,const value_type& x)
        {return vec_.insert(p,x);}
    bool KeyCompare_Leq_(const K& ty0,const K& ty1)
        {return !key_compare_(ty1,ty0);}
    bool KeyCompare_Geq_(const K& ty0,const K& ty1)
        {return !key_compare_(ty0,ty1);}
    bool KeyCompare_Gt_(const K& ty0,const K& ty1)
        {return key_compare_(ty1,ty0);}

    key_compare         key_compare_;
    Cont                vec_;
};


template<class K,bool bNoDuplicates,class Pr, class A> inline
	bool operator==(const sorted_vector<K, bNoDuplicates,Pr,A>& x,
		            const sorted_vector<K, bNoDuplicates,Pr,A>& Y_)
	{return x.Eq_(Y_); }
template<class K,bool bNoDuplicates,class Pr, class A> inline
	bool operator!=(const sorted_vector<K, bNoDuplicates,Pr,A>& x,
		            const sorted_vector<K, bNoDuplicates,Pr,A>& Y_)
	{return !(x == Y_); }
template<class K,bool bNoDuplicates,class Pr, class A> inline
	bool operator<(const sorted_vector<K, bNoDuplicates,Pr,A>& x,
		            const sorted_vector<K, bNoDuplicates,Pr,A>& Y_)
	{return x.Lt_(Y_);}
template<class K,bool bNoDuplicates,class Pr,class A> inline
	bool operator>(const sorted_vector<K, bNoDuplicates,Pr,A>& x,
		            const sorted_vector<K, bNoDuplicates,Pr,A>& Y_)
	{return Y_ < x; }
template<class K,bool bNoDuplicates,class Pr, class A> inline
	bool operator<=(const sorted_vector<K, bNoDuplicates,Pr,A>& x,
		            const sorted_vector<K, bNoDuplicates,Pr,A>& Y_)
	{return !(Y_ < x); }
template<class K, bool bNoDuplicates,class Pr,class A> inline
	bool operator>=(const sorted_vector<K, bNoDuplicates,Pr,A>& x,
		            const sorted_vector<K, bNoDuplicates,Pr,A>& Y_)
	{return (!(x < Y_)); }

//#pragma warning(pop)
//#pragma pack(pop)
#elif VERSION_SORTED_VECTOR_ != 0x00010010
#error You have included two sorted_vector.h with different version numbers
#endif
