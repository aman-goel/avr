/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


#ifndef hashcons_hpp
#define hashcons_hpp

#include <unordered_map>
#include <memory>

template <class T>
class hashcons {
  using key_type  = typename T::key_type;
  using key_hash  = typename T::key_hash;
  using key_equal = typename T::key_equal;
  
  std::unordered_map<key_type, std::weak_ptr<T>, key_hash, key_equal> instances;
  
public:
  template <class ... Args>
  std::shared_ptr<T> operator()(Args&& ... args) {
    key_type key = T::make_key(args...);
    auto it = instances.find(key);
    if (it != instances.end()) {
      if (std::shared_ptr<T> existing = it->second.lock()) {
        return existing;
      } else {
        instances.erase(key);
      }
    }
    std::shared_ptr<T> new_instance(new T(args...), [this,key] (T *x) { instances.erase(key); delete x; } );
    instances.insert({key, new_instance});
    return new_instance;
  }


  // You can use get() in order to know whether the underlying object was freshly built (true)
  // or if we are reusing an existing instance (false).
  template <class ... Args>
  std::pair<bool, std::shared_ptr<T>> get(Args&& ... args) {
    key_type key = T::make_key(args...);
    auto it = instances.find(key);
    if (it != instances.end()) {
      if (std::shared_ptr<T> existing = it->second.lock()) {
        return {false, existing};
      } else {
        instances.erase(key);
      }
    }
    std::shared_ptr<T> new_instance(new T(args...), [this,key] (T *x) { instances.erase(key); delete x; } );
    instances.insert({key, new_instance});
    return {true, new_instance};
  }

};



// can be use eg for hashcons_std<string>
template <class T,
          class key_type = std::size_t,
          class make_key = std::hash<T>>
class hashcons_std {

  std::unordered_map<key_type, std::weak_ptr<T>, std::hash<key_type>, std::equal_to<key_type>> instances;

public:
  template <class ... Args>
  std::shared_ptr<T> operator()(Args&& ... args) {
    key_type key = make_key()(args...);
    auto it = instances.find(key);
    if (it != instances.end()) {
      if (std::shared_ptr<T> existing = it->second.lock()) {
        return existing;
      } else {
        instances.erase(key);
      }
    }
    std::shared_ptr<T> new_instance(new T(args...), [this,key] (T *x) { instances.erase(key); delete x; } );
    instances.insert({key, new_instance});
    return new_instance;
  }

};




#endif /* hashcons_hpp */
