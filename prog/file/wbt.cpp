#include <vector>
#include <cstdlib>

namespace wbt {

template<typename Data>
struct Node;

template<typename Data>
using NodePtr = Node<Data> *;

template<typename Data>
struct Node {
  size_t refcnt;
  size_t size;
  NodePtr<Data> left;
  Data data;
  NodePtr<Data> right;
  Node(NodePtr<Data> left, Data data, NodePtr<Data> right);
  Node(NodePtr<Data> left, Data data, NodePtr<Data> right, size_t size);
  Node() = default;
  void *operator new(size_t size);
};

size_t pool_size = 1024;
std::vector<Node<long long> *> pool = {(Node<long long> *)malloc(sizeof(Node<long long>) * pool_size)};
size_t pool_sp0 = 0;
size_t pool_sp1 = 0;

template<typename Data>
inline void *Node<Data>::operator new(size_t size) {
  void *ret = (void *)&pool[pool_sp0][pool_sp1++];
  if (pool_sp1 >= pool_size) {
    pool_size <<= 1;
    pool.emplace_back((Node<long long> *)malloc(sizeof(Node<long long>) * pool_size));
    pool_sp0 += 1;
    pool_sp1 = 0;
  }
  return ret;
}

template<typename Data>
inline size_t size(NodePtr<Data> t) {
  if (t != nullptr) {
    return t->size;
  } else {
    return 0;
  }
}

template<typename Data>
inline void incref(NodePtr<Data> a) {
  if (a != nullptr)
    a->refcnt += 1;
}

template<typename Data>
inline void decref(NodePtr<Data> a) {
  if (a != nullptr)
    a->refcnt -= 1;
}
template<typename Data>
inline Node<Data>::Node(NodePtr<Data> left, Data data, NodePtr<Data> right)
  : left(left), data(data), right(right), refcnt(0) {
  incref(left);
  incref(right);
  size = 1 + wbt::size(left) + wbt::size(right);
}

template<typename Data>
inline Node<Data>::Node(NodePtr<Data> left, Data data, NodePtr<Data> right, size_t size)
: left(left), data(data), right(right), refcnt(0), size(size) {
  incref(left);
  incref(right);
}

template<typename Data>
inline NodePtr<Data> singleLeft(NodePtr<Data> a) {
  NodePtr<Data>
    b = a->right,
    x = a->left,
    y = b->left,
    z = b->right;
  if (a->refcnt == 0 && b->refcnt == 1) {
    b->size = a->size;
    a->size -= size(z) + 1;
    a->right = y;
    b->left = a;
    a->refcnt = 1;
    b->refcnt = 0;
    return b;
  } else if (a->refcnt == 0) {
    size_t all_size = a->size;
    a->size -= size(z) + 1;
    a->right = y;
    incref(y);
    decref(b);
    return new Node(a, b->data, z, all_size);
  } else {
    return new Node(new Node(x, a->data, y, a->size - size(z) - 1),
                    b->data,
                    z,
                    a->size);
  }
}

template<typename Data>
inline NodePtr<Data> singleRight(NodePtr<Data> b) {
  NodePtr<Data>
    a = b->left,
    x = a->left,
    y = a->right,
    z = b->right;
  if (b->refcnt == 0 && a->refcnt == 1) {
    a->size = b->size;
    b->size -= size(x) + 1;
    b->left = y;
    a->right = b;
    b->refcnt = 1;
    a->refcnt = 0;
    return a;
  } else if (b->refcnt == 0) {
    size_t all_size = b->size;
    b->size -= size(x) + 1;
    b->left = y;
    incref(y);
    decref(a);
    return new Node(x, a->data, b, all_size);
  } else {
    return new Node(x,
                    a->data,
                    new Node(y, b->data, z, b->size - size(x) - 1),
                    b->size);
  }
}

template<typename Data>
inline NodePtr<Data> doubleLeft(NodePtr<Data> a) {
  NodePtr<Data>
    x = a->left,
    c = a->right,
    b = c->left,
    y = b->left,
    z = b->right,
    w = c->right;
  if (a->refcnt == 0 && c->refcnt == 1 && b->refcnt == 1) {
    size_t y_size = size(y);
    b->size = a->size;
    a->size += - c->size + y_size;
    c->size -= y_size + 1;
    a->right = y;
    c->left = z;
    b->left = a;
    b->right = c;
    a->refcnt = 1;
    b->refcnt = 0;
    return b;
  } else if (a->refcnt == 0 && c->refcnt == 1) {
    size_t
      all_size = a->size,
      y_size = size(y);
    a->size += - c->size + y_size;
    c->size -= y_size + 1;
    a->right = y;
    c->left = z;
    c->refcnt = 0;
    incref(y);
    incref(z);
    decref(b);
    return new Node(a, b->data, c, all_size);
  } else if (a->refcnt == 0) {
    size_t
      all_size = a->size,
      y_size = size(y);
    a->size += - c->size + y_size;
    a->right = y;
    incref(y);
    decref(c);
    return new Node(a,
                    b->data,
                    new Node(z, c->data, w, c->size - y_size - 1),
                    all_size);
  } else {
    size_t y_size = size(y);
    return new Node(new Node(x, a->data, y, a->size - c->size + y_size),
                    b->data,
                    new Node(z, c->data, w, c->size - y_size - 1),
                    a->size);
  }
}

template<typename Data>
inline NodePtr<Data> doubleRight(NodePtr<Data> c) {
  NodePtr<Data>
    a = c->left,
    x = a->left,
    b = a->right,
    y = b->left,
    z = b->right,
    w = c->right;
  if (c->refcnt == 0 && a->refcnt == 1 && b->refcnt == 1) {
    size_t z_size = size(z);
    b->size = c->size;
    c->size += - a->size + z_size;
    a->size -= z_size + 1;
    c->left = z;
    a->right = y;
    b->left = a;
    b->right = c;
    c->refcnt = 1;
    b->refcnt = 0;
    return b;
  } else if (c->refcnt == 0 && a->refcnt == 1) {
    size_t
      all_size = c->size,
      z_size = size(z);
    c->size += - a->size + z_size;
    a->size -= z_size + 1;
    a->right = y;
    c->left = z;
    a->refcnt = 0;
    incref(y);
    incref(z);
    decref(b);
    return new Node(a, b->data, c, all_size);
  } else if (c->refcnt == 0) {
    size_t
      all_size = c->size,
      z_size = size(z);
    c->size += - a->size + z_size;
    c->left = z;
    incref(z);
    decref(a);
    return new Node(new Node(x, a->data, y, a->size - z_size - 1),
                    b->data,
                    c,
                    all_size);
  } else {
    size_t z_size = size(z);
    return new Node(new Node(x, a->data, y, a->size - z_size - 1),
                    b->data,
                    new Node(z, c->data, w, c->size - a->size + z_size),
                    c->size);
  }
}

// a < b
template<typename Data>
inline bool isBalanced(NodePtr<Data> a, NodePtr<Data> b) {
  return 5 * (size(a) + 1) >= 2 * (size(b) + 1);
}

template<typename Data>
inline bool isSingle(NodePtr<Data> a, NodePtr<Data> b) {
  return 2 * (size(a) + 1) < 3 * (size(b) + 1);
}

// t->left < t->right
template<typename Data>
inline NodePtr<Data> balanceLeft(NodePtr<Data> t) {
  if (isBalanced(t->left, t->right)) {
    return t;
  } else if (isSingle(t->right->left, t->right->right)) {
    return singleLeft(t);
  } else {
    return doubleLeft(t);
  }
}

// t->left > t->right
template<typename Data>
inline NodePtr<Data> balanceRight(NodePtr<Data> t) {
  if (isBalanced(t->right, t->left)) {
    return t;
  } else if (isSingle(t->left->right, t->left->left)) {
    return singleRight(t);
  } else {
    return doubleRight(t);
  }
}

template<typename Data, class Compare>
static NodePtr<Data> insert(Data v, NodePtr<Data> t, const Compare &cmp, size_t &pos) {
  if (t == nullptr) {
    return new Node<Data>(nullptr, v, nullptr, 1);
  } else if (cmp(v, t->data)) {
    if (t->refcnt == 0) {
      decref(t->left);
      t->left = insert(v, t->left, cmp, pos);
      t->size = 1 + size(t->left) + size(t->right);
      t->left->refcnt += 1;
      return balanceRight(t);
    } else {
      return balanceRight(new Node(insert(v, t->left, cmp, pos),
                                   t->data,
                                   t->right));
    }
  } else if (cmp(t->data, v)) {
    pos += size(t->left) + 1;
    if (t->refcnt == 0) {
      decref(t->right);
      t->right = insert(v, t->right, cmp, pos);
      t->size = 1 + size(t->left) + size(t->right);
      t->right->refcnt += 1;
      return balanceLeft(t);
    } else {
      return balanceLeft(new Node(t->left,
                                  t->data,
                                  insert(v, t->right, cmp, pos)));
    }
  } else {
    return t;
  }
}

template<typename Data>
static NodePtr<Data> removeMin(NodePtr<Data> t, Data &v) {
  if (t->refcnt == 0) {
    if (t->left == nullptr) {
      v = t->data;
      NodePtr<Data> ret = t->right;
      decref(ret);
      return ret;
    } else {
      t->size -= 1;
      t->left->refcnt -= 1;
      t->left = removeMin(t->left, v);
      incref(t->left);
      return balanceLeft(t);
    }
  } else {
    if (t->left == nullptr) {
      v = t->data;
      return t->right;
    } else {
      return balanceLeft(new Node(removeMin(t->left, v),
                                  t->data,
                                  t->right,
                                  t->size - 1));
    }
  }
}

template<typename Data, class Compare>
static NodePtr<Data> remove(const Data &v, NodePtr<Data> t, const Compare &cmp) {
  if (t == nullptr) {
    return nullptr;
  } else if (cmp(v, t->data)) {
    if (t->refcnt == 0) {
      decref(t->left);
      t->left = remove(v, t->left, cmp);
      t->size = 1 + size(t->left) + size(t->right);
      incref(t->left);
      return balanceLeft(t);
    } else {
      return balanceLeft(new Node(remove(v, t->left, cmp),
                                  t->data,
                                  t->right));
    }
  } else if (cmp(t->data, v)) {
    if (t->refcnt == 0) {
      decref(t->right);
      t->right = remove(v, t->right, cmp);
      t->size = 1 + size(t->left) + size(t->right);
      incref(t->right);
      return balanceRight(t);
    } else {
      return balanceRight(new Node(t->left,
                                   t->data,
                                   remove(v, t->right, cmp)));
    }
  } else {
    if (t->refcnt == 0) {
      if (t->left == nullptr) {
        NodePtr<Data> ret = t->right;
        decref(ret);
        return ret;
      } else if (t->right == nullptr) {
        NodePtr<Data> ret = t->left;
        decref(ret);
        return ret;
      } else {
        t->right->refcnt -= 1;
        t->right = removeMin(t->right, t->data);
        t->size -= 1;
        incref(t->right);
        return balanceRight(t);
      }
    } else {
      if (t->left == nullptr) {
        return t->right;
      } else if (t->right == nullptr) {
        return t->left;
      } else {
        Data min;
        NodePtr<Data> r = removeMin(t->right, min);
        return balanceRight(new Node(t->left,
                                     min,
                                     r,
                                     t->size - 1));
      }
    }
  }
}

template<typename Data>
static Data &at(size_t p, NodePtr<Data> t) {
  size_t sz = size(t->left);
  if (sz == p) {
    return t->data;
  } else if (sz < p) {
    return at(p - sz - 1, t->right);
  } else {
    return at(p, t->left);
  }
}

template<typename Data, class Compare>
static size_t nle(const Data &v, NodePtr<Data> t, const Compare &cmp) {
  if (t == nullptr) {
    return 0;
  } else if (cmp(v, t->data)) {
    return nle(v, t->left, cmp);
  } else {
    return 1 + size(t->left) + nle(v, t->right, cmp);
  }
}

template<typename Data, class Compare>
static size_t nge(const Data &v, NodePtr<Data> t, const Compare &cmp) {
  if (t == nullptr) {
    return 0;
  } else if (cmp(t->data, v)) {
    return nge(v, t->right, cmp);
  } else {
    return 1 + size(t->right) + nge(v, t->left, cmp);
  }
}

template<typename Data, class Compare>
inline size_t nbetween(const Data &a, const Data &b, NodePtr<Data> t, const Compare &cmp) {
  return nle(b, t, cmp) + nge(a, t, cmp) - size(t);
}

template<typename Data, class Compare>
static bool member(const Data &v, NodePtr<Data> t, const Compare &cmp, size_t &pos) {
  if (t == nullptr) {
    return false;
  } else if (cmp(v, t->data)) {
    return member(v, t->left, cmp, pos);
  } else if (cmp(t->data, v)) {
    pos += size(t->left) + 1;
    return member(v, t->right, cmp, pos);
  } else {
    pos += size(t->left);
    return true;
  }
}

template<typename Data>
static void freeTree(NodePtr<Data> t) {
  if (t != nullptr) {
    if (t->refcnt == 0) {
      decref(t->left);
      decref(t->right);
      freeTree(t->left);
      freeTree(t->right);
    }
  }
}

}

template<typename Data, class Compare = std::less<Data>>
class ESet {
private:
  wbt::NodePtr<Data> root;
  Compare cmp;
public:
  class iterator {
    friend class ESet;
  private:
    const ESet *iteratee;
    iterator(const ESet *iteratee, size_t index) : iteratee(iteratee), index(index) {}
  public:
    size_t index;
    iterator() = default;
    iterator(const iterator &other) = default;

    iterator &operator=(const iterator &other) = default;
    
    iterator &operator+=(const size_t &n) {
      index += n;
      return *this;
    }

    iterator &operator-=(const size_t &n) {
      return (*this += (-n));
    }

    iterator operator+(const size_t &n) const {
      iterator tmp = *this;
      return tmp += n;
    }

    iterator operator-(const size_t &n) const {
      return (*this + (-n));
    }

    iterator operator++(int) {
      iterator tmp = *this;
      *this += 1;
      return tmp;
    }

    iterator operator--(int) {
      iterator tmp = *this;
      *this -= 1;
      return tmp;
    }

    iterator &operator++() {
      return *this += 1;
    }

    iterator &operator--() {
      return *this -= 1;
    }

    Data operator*() const {
      return iteratee->at(index);
    }

    bool operator==(const iterator &other) const {
      return iteratee == other.iteratee && index == other.index;
    }

    bool operator!=(const iterator &other) const {
      return !(*this == other);
    }
  };

  friend class iterator;

  iterator begin() const {
    return iterator(this, 0);
  }

  iterator end() const {
    return iterator(this, size());
  }

  ESet() : cmp(Compare()), root(nullptr) {}
  ESet(const ESet &other) : cmp(other.cmp), root(other.root) {
    wbt::incref(root);
  }
  ESet(ESet &&other) : cmp(other.cmp), root(other.root) {}
  ~ESet() {
    wbt::decref(root);
    wbt::freeTree(root);
  }

  ESet &operator=(const ESet &other) {
    wbt::decref(root);
    root = other.root;
    wbt::incref(root);
    return *this;
  }

  ESet &operator=(ESet &&other) {
    wbt::decref(root);
    root = other.root;
    return *this;
  }

  template<class... Args>
  std::pair<iterator, bool> emplace(Args&&... args) {
    wbt::decref(root);
    size_t pos = 0;
    size_t osize = wbt::size(root);
    root = wbt::insert(Data(args...), root, cmp, pos);
    wbt::incref(root);
    if (osize == root->size) {
      return {end(), false};
    } else {
      return {iterator(this, pos), true};
    }
  }

  size_t erase(const Data &v) {
    wbt::decref(root);
    size_t osize = wbt::size(root);
    root = wbt::remove(v, root, cmp);
    wbt::incref(root);
    return osize - wbt::size(root);
  }

  size_t size() const {
    return wbt::size(root);
  }

  bool empty() const {
    return root == nullptr;
  }

  iterator find(const Data &a) const {
    size_t pos = 0;
    if (wbt::member(a, root, cmp, pos)) {
      return iterator(this, pos);
    } else {
      return end();
    }
  }

  size_t range(const Data &a, const Data &b) const {
    return wbt::nbetween(a, b, root, cmp);
  }

  iterator lower_bound(const Data &a) const {
    return iterator(this, size(root) - wbt::nge(a, root, cmp));
  }

  iterator upper_bound(const Data &a) const {
    return iterator(this, wbt::nle(a, root, cmp));
  }

  Data at(size_t pos) const {
    return wbt::at(pos, root);
  }

  Data operator[](size_t pos) const {
    return at(pos);
  }
};
