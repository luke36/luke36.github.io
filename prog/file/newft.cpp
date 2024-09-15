#include <cstddef>

struct Node {
  char nchild;
  size_t size;
  Node(char nchild, size_t size) : nchild(nchild), size(size) {}
};

template <class Data>
struct Leaf : Node {
  Data data;
  Leaf(const Data &data)
    : Node(0, 1), data(data) {}
};

struct Node2 : Node {
  Node *c1;
  Node *c2;
  Node2(Node *c1, Node *c2)
    : Node(2, c1->size + c2->size), c1(c1), c2(c2) {}
};

struct Node3 : Node {
  Node *c1;
  Node *c2;
  Node *c3;
  Node3(Node *c1, Node *c2, Node *c3)
    : Node(3, c1->size + c2->size + c3->size), c1(c1), c2(c2), c3(c3) {}
};

struct Digit {
  char nchild;
  size_t size;
  Digit(char nchild, size_t size) : nchild(nchild), size(size) {}
};

struct Digit1 : Digit {
  Node *c1;
  Digit1(Node *f1)
    : Digit(1, f1->size), c1(f1) {}
};

struct Digit2 : Digit {
  Node *c1;
  Node *c2;
  Digit2(Node *f1, Node *f2)
    : Digit(2, f1->size + f2->size), c1(f1), c2(f2) {}
};

struct Digit3 : Digit {
  Node *c1;
  Node *c2;
  Node *c3;
  Digit3(Node *f1, Node *f2, Node *f3)
    : Digit(3, f1->size + f2->size + f3->size), c1(f1), c2(f2), c3(f3) {}
};

struct Digit4 : Digit {
  Node *c1;
  Node *c2;
  Node *c3;
  Node *c4;
  Digit4(Node *f1, Node *f2, Node *f3, Node *f4)
    : Digit(4, f1->size + f2->size + f3->size + f4->size), c1(f1), c2(f2), c3(f3), c4(f4) {}
};

struct Tree {
  size_t size;
  Node *single;
  Digit *fingerl;
  Tree *deep;
  Digit *fingerr;
  Tree(Node *single)
    : size(single->size), single(single), deep(nullptr) {}
  Tree(Digit *fingerl, Tree *deep, Digit *fingerr)
    : size((fingerl == nullptr ? 0 : fingerl->size) +
           (deep == nullptr ? 0 : deep->size) +
           (fingerr == nullptr ? 0 : fingerr->size)),
      single(nullptr), fingerl(fingerl), deep(deep), fingerr(fingerr) {}
};

static inline Digit *pushNodeFrontDigit(Node *a, Digit *d) {
  if (d->nchild == 3) {
    Digit3 *dgt = static_cast<Digit3 *>(d);
    Node
      *b = dgt->c1,
      *c = dgt->c2,
      *d = dgt->c3;
    delete dgt;
    return new Digit4(a, b, c, d);
  } else if (d->nchild == 2) {
    Digit2 *dgt = static_cast<Digit2 *>(d);
    Node
      *b = dgt->c1,
      *c = dgt->c2;
    delete dgt;
    return new Digit3(a, b, c);
  } else {
    Digit1 *dgt = static_cast<Digit1 *>(d);
    Node
      *b = dgt->c1;
    delete dgt;
    return new Digit2(a, b);
  }
}

static Tree *pushNodeFront(Node *a, Tree *t) {
  if (t == nullptr) {
    return new Tree(a);
  } else if (t->single != nullptr) {
    t->size += a->size;
    t->fingerl = new Digit1(a);
    t->fingerr = new Digit1(t->single);
    t->single = nullptr;
    return t;
  } else if (t->fingerl->nchild == 4) {
    t->size += a->size;
    Digit4 *fl = static_cast<Digit4 *>(t->fingerl);
    Node
      *b = fl->c1,
      *c = fl->c2,
      *d = fl->c3,
      *e = fl->c4;
    t->deep = pushNodeFront(new Node3(c, d, e), t->deep);
    delete t->fingerl;
    t->fingerl = new Digit2(a, b);
    return t;
  } else {
    t->size += a->size;
    t->fingerl = pushNodeFrontDigit(a, t->fingerl);
    return t;
  }
}

template<class Data>
static inline Tree *pushFront(const Data &v, Tree *t) {
  return pushNodeFront(new Leaf(v), t);
}

static inline Digit *pushNodeBackDigit(Digit *d, Node *a) {
  if (d->nchild == 3) {
    Digit3 *dgt = static_cast<Digit3 *>(d);
    Node
      *d = dgt->c1,
      *c = dgt->c2,
      *b = dgt->c3;
    delete dgt;
    return new Digit4(d, c, b, a);
  } else if (d->nchild == 2) {
    Digit2 *dgt = static_cast<Digit2 *>(d);
    Node
      *c = dgt->c1,
      *b = dgt->c2;
    delete dgt;
    return new Digit3(c, b, a);
  } else {
    Digit1 *dgt = static_cast<Digit1 *>(d);
    Node
      *b = dgt->c1;
    delete dgt;
    return new Digit2(b, a);
  }
}

static Tree *pushNodeBack(Tree *t, Node *a) {
  if (t == nullptr) {
    return new Tree(a);
  } else if (t->single != nullptr) {
    t->size += a->size;
    t->fingerl = new Digit1(t->single);
    t->fingerr = new Digit1(a);
    t->single = nullptr;
    return t;
  } else if (t->fingerr->nchild == 4) {
    t->size += a->size;
    Digit4 *fr = static_cast<Digit4 *>(t->fingerr);
    Node
      *e = fr->c1,
      *d = fr->c2,
      *c = fr->c3,
      *b = fr->c4;
    t->deep = pushNodeBack(t->deep, new Node3(e, d, c));
    delete t->fingerr;
    t->fingerr = new Digit2(b, a);
    return t;
  } else {
    t->size += a->size;
    t->fingerr = pushNodeBackDigit(t->fingerr, a);
    return t;
  }
}

template<class Data>
static inline Tree *pushBack(Tree *t, const Data &v) {
  return pushNodeBack(t, new Leaf(v));
}

static inline Tree *digitToTree(Tree *old, Digit *a) {
  old->size = a->size;
  if (a->nchild == 1) {
    Digit1 *dgt = static_cast<Digit1 *>(a);
    old->single = dgt->c1;
    delete dgt;
    return old;
  } else if (a->nchild == 2) {
    Digit2 *dgt = static_cast<Digit2 *>(a);
    Node
      *a = dgt->c1,
      *b = dgt->c2;
    delete dgt;
    old->fingerl = new Digit1(a);
    old->fingerr = new Digit1(b);
    return old;
  } else if (a->nchild == 3) {
    Digit3 *dgt = static_cast<Digit3 *>(a);
    Node
      *a = dgt->c1,
      *b = dgt->c2,
      *c = dgt->c3;
    delete dgt;
    old->fingerl = new Digit2(a, b);
    old->fingerr = new Digit1(c);
    return old;
  } else {
    Digit4 *dgt = static_cast<Digit4 *>(a);
    Node
      *a = dgt->c1,
      *b = dgt->c2,
      *c = dgt->c3,
      *d = dgt->c4;
    delete dgt;
    old->fingerl = new Digit2(a, b);
    old->fingerr = new Digit2(c, d);
    return old;
  }
}

static inline Digit *nodeToDigit(Node *a) {
  if (a->nchild == 2) {
    Node2 *a2 = static_cast<Node2 *>(a);
    Node
      *a = a2->c1,
      *b = a2->c2;
    delete a2;
    return new Digit2(a, b);
  } else {
    Node3 *a3 = static_cast<Node3 *>(a);
    Node
      *a = a3->c1,
      *b = a3->c2,
      *c = a3->c3;
    delete a3;
    return new Digit3(a, b, c);
  }
}

static inline Digit *popFrontDigit(Node *&h, Digit *a) {
  if (a->nchild == 1) {
    Digit1 *dgt = static_cast<Digit1 *>(a);
    h = dgt->c1;
    delete a;
    return nullptr;
  } else if (a->nchild == 2) {
    Digit2 *dgt = static_cast<Digit2 *>(a);
    Node
      *a = dgt->c1,
      *b = dgt->c2;
    delete dgt;
    h = a;
    return new Digit1(b);
  } else if (a->nchild == 3) {
    Digit3 *dgt = static_cast<Digit3 *>(a);
    Node
      *a = dgt->c1,
      *b = dgt->c2,
      *c = dgt->c3;
    delete dgt;
    h = a;
    return new Digit2(b, c);
  } else {
    Digit4 *dgt = static_cast<Digit4 *>(a);
    Node
      *a = dgt->c1,
      *b = dgt->c2,
      *c = dgt->c3,
      *d = dgt->c4;
    delete dgt;
    h = a;
    return new Digit3(b, c, d);
  }
}

static Tree *popNodeFront(Node *&a, Tree *t) {
  if (t->single != nullptr) {
    a = t->single;
    delete t;
    return nullptr;
  } else {
    t->fingerl = popFrontDigit(a, t->fingerl);
    t->size -= a->size;
    if (t->fingerl == nullptr) {
      if (t->deep == nullptr) {
        return digitToTree(t, t->fingerr);
      } else {
        Node *h;
        t->deep = popNodeFront(h, t->deep);
        t->fingerl = nodeToDigit(h);
        return t;
      }
    } else {
      return t;
    }
  }
}

template<class Data>
static inline Tree *popFront(Tree *t) {
  Node *x;
  t = popNodeFront(x, t);
  delete static_cast<Leaf<Data> *>(x);
  return t;
}

static inline Digit *popBackDigit(Digit *a, Node *&t) {
  if (a->nchild == 1) {
    Digit1 *dgt = static_cast<Digit1 *>(a);
    t = dgt->c1;
    delete a;
    return nullptr;
  } else if (a->nchild == 2) {
    Digit2 *dgt = static_cast<Digit2 *>(a);
    Node
      *b = dgt->c1,
      *a = dgt->c2;
    delete dgt;
    t = a;
    return new Digit1(b);
  } else if (a->nchild == 3) {
    Digit3 *dgt = static_cast<Digit3 *>(a);
    Node
      *c = dgt->c1,
      *b = dgt->c2,
      *a = dgt->c3;
    delete dgt;
    t = a;
    return new Digit2(c, b);
  } else {
    Digit4 *dgt = static_cast<Digit4 *>(a);
    Node
      *d = dgt->c1,
      *c = dgt->c2,
      *b = dgt->c3,
      *a = dgt->c4;
    delete dgt;
    t = a;
    return new Digit3(d, c, b);
  }
}

static Tree *popNodeBack(Tree *t, Node *&a) {
  if (t->single != nullptr) {
    a = t->single;
    delete t;
    return nullptr;
  } else {
    t->fingerr = popBackDigit(t->fingerr, a);
    t->size -= a->size;
    if (t->fingerr == nullptr) {
      if (t->deep == nullptr) {
        return digitToTree(t, t->fingerl);
      } else {
        Node *b;
        t->deep = popNodeBack(t->deep, b);
        t->fingerr = nodeToDigit(b);
        return t;
      }
    } else {
      return t;
    }
  }
}

template<class Data>
static inline Tree *popBack(Tree *t) {
  Node *x;
  t = popNodeBack(t, x);
  delete static_cast<Leaf<Data> *>(x);
  return t;
}

template<class Data>
static Data &atNode(Node *a, size_t pos) {
  if (a->nchild == 2) {
    Node2 *a2 = static_cast<Node2 *>(a);
    Node
      *a = a2->c1,
      *b = a2->c2;
    if (pos < a->size) {
      return atNode<Data>(a, pos);
    } else {
      return atNode<Data>(b, pos - a->size);
    }
  } else if (a->nchild == 3) {
    Node3 *a3 = static_cast<Node3 *>(a);
    Node
      *a = a3->c1,
      *b = a3->c2,
      *c = a3->c3;
    if (pos < a->size) {
      return atNode<Data>(a, pos);
    }
    pos -= a->size;
    if (pos < b->size) {
      return atNode<Data>(b, pos);
    }
    pos -= b->size;
    return atNode<Data>(c, pos);
  } else {
    return static_cast<Leaf<Data> *>(a)->data;
  }
}

template<class Data>
static Data &atDigit(Digit *a, size_t pos) {
  if (a->nchild == 1) {
    return atNode<Data>(static_cast<Digit1 *>(a)->c1, pos);
  } else if (a->nchild == 2) {
    Digit2 *dgt = static_cast<Digit2 *>(a);
    Node
      *a = dgt->c1,
      *b = dgt->c2;
    if (pos < a->size) {
      return atNode<Data>(a, pos);
    } else {
      return atNode<Data>(b, pos - a->size);
    }
  } else if (a->nchild == 3) {
    Digit3 *dgt = static_cast<Digit3 *>(a);
    Node
      *a = dgt->c1,
      *b = dgt->c2,
      *c = dgt->c3;
    if (pos < a->size) {
      return atNode<Data>(a, pos);
    }
    pos -= a->size;
    if (pos < b->size) {
      return atNode<Data>(b, pos);
    }
    pos -= b->size;
    return atNode<Data>(c, pos);
  } else {
    Digit4 *dgt = static_cast<Digit4 *>(a);
    Node
      *a = dgt->c1,
      *b = dgt->c2,
      *c = dgt->c3,
      *d = dgt->c4;
    if (pos < a->size) {
      return atNode<Data>(a, pos);
    }
    pos -= a->size;
    if (pos < b->size) {
      return atNode<Data>(b, pos);
    }
    pos -= b->size;
    if (pos < c->size) {
      return atNode<Data>(c, pos);
    }
    pos -= c->size;
    return atNode<Data>(d, pos);
  }
}

template<class Data>
static Data &at(Tree *t, size_t pos) {
  if (t->single != nullptr) {
    return atNode<Data>(t->single, pos);
  } else {
    size_t sizel = t->fingerl->size;
    if (pos < sizel) {
      return atDigit<Data>(t->fingerl, pos);
    } else {
      pos -= sizel;
      size_t sized = t->deep == nullptr ? 0 : t->deep->size;
      if (pos < sized) {
        return at<Data>(t->deep, pos);
      } else {
        pos -= sized;
        return atDigit<Data>(t->fingerr, pos);
      }
    }
  }
}

static inline Digit *digitsToDigit(Digit *x, Digit *y, Digit *z) {
  if (x->nchild == 1) {
    Digit1 *x_ = static_cast<Digit1 *>(x);
    Node *c1 = x_->c1;
    delete x_;
    if (y == nullptr) {
      if (z->nchild == 1) {
        Digit1 *z_ = static_cast<Digit1 *>(z);
        Node *c2 = z_->c1;
        delete z_;
        Node *_c1 = new Node2(c1, c2);
        return new Digit1(_c1);
      } else if (z->nchild == 2) {
        Digit2 *z_ = static_cast<Digit2 *>(z);
        Node *c2 = z_->c1;
        Node *c3 = z_->c2;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        return new Digit1(_c1);
      } else if (z->nchild == 3) {
        Digit3 *z_ = static_cast<Digit3 *>(z);
        Node *c2 = z_->c1;
        Node *c3 = z_->c2;
        Node *c4 = z_->c3;
        delete z_;
        Node *_c1 = new Node2(c1, c2);
        Node *_c2 = new Node2(c3, c4);
        return new Digit2(_c1, _c2);
      } else {
        Digit4 *z_ = static_cast<Digit4 *>(z);
        Node *c2 = z_->c1;
        Node *c3 = z_->c2;
        Node *c4 = z_->c3;
        Node *c5 = z_->c4;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node2(c4, c5);
        return new Digit2(_c1, _c2);
      }
    } else if (y->nchild == 1) {
      Digit1 *y_ = static_cast<Digit1 *>(y);
      Node *c2 = y_->c1;
      delete y_;
      if (z->nchild == 1) {
        Digit1 *z_ = static_cast<Digit1 *>(z);
        Node *c3 = z_->c1;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        return new Digit1(_c1);
      } else if (z->nchild == 2) {
        Digit2 *z_ = static_cast<Digit2 *>(z);
        Node *c3 = z_->c1;
        Node *c4 = z_->c2;
        delete z_;
        Node *_c1 = new Node2(c1, c2);
        Node *_c2 = new Node2(c3, c4);
        return new Digit2(_c1, _c2);
      } else if (z->nchild == 3) {
        Digit3 *z_ = static_cast<Digit3 *>(z);
        Node *c3 = z_->c1;
        Node *c4 = z_->c2;
        Node *c5 = z_->c3;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node2(c4, c5);
        return new Digit2(_c1, _c2);
      } else {
        Digit4 *z_ = static_cast<Digit4 *>(z);
        Node *c3 = z_->c1;
        Node *c4 = z_->c2;
        Node *c5 = z_->c3;
        Node *c6 = z_->c4;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node3(c4, c5, c6);
        return new Digit2(_c1, _c2);
      }
    } else if (y->nchild == 2) {
      Digit2 *y_ = static_cast<Digit2 *>(y);
      Node *c2 = y_->c1;
      Node *c3 = y_->c2;
      delete y_;
      if (z->nchild == 1) {
        Digit1 *z_ = static_cast<Digit1 *>(z);
        Node *c4 = z_->c1;
        delete z_;
        Node *_c1 = new Node2(c1, c2);
        Node *_c2 = new Node2(c3, c4);
        return new Digit2(_c1, _c2);
      } else if (z->nchild == 2) {
        Digit2 *z_ = static_cast<Digit2 *>(z);
        Node *c4 = z_->c1;
        Node *c5 = z_->c2;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node2(c4, c5);
        return new Digit2(_c1, _c2);
      } else if (z->nchild == 3) {
        Digit3 *z_ = static_cast<Digit3 *>(z);
        Node *c4 = z_->c1;
        Node *c5 = z_->c2;
        Node *c6 = z_->c3;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node3(c4, c5, c6);
        return new Digit2(_c1, _c2);
      } else {
        Digit4 *z_ = static_cast<Digit4 *>(z);
        Node *c4 = z_->c1;
        Node *c5 = z_->c2;
        Node *c6 = z_->c3;
        Node *c7 = z_->c4;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node2(c4, c5);
        Node *_c3 = new Node2(c6, c7);
        return new Digit3(_c1, _c2, _c3);
      }
    } else if (y->nchild == 3) {
      Digit3 *y_ = static_cast<Digit3 *>(y);
      Node *c2 = y_->c1;
      Node *c3 = y_->c2;
      Node *c4 = y_->c3;
      delete y_;
      if (z->nchild == 1) {
        Digit1 *z_ = static_cast<Digit1 *>(z);
        Node *c5 = z_->c1;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node2(c4, c5);
        return new Digit2(_c1, _c2);
      } else if (z->nchild == 2) {
        Digit2 *z_ = static_cast<Digit2 *>(z);
        Node *c5 = z_->c1;
        Node *c6 = z_->c2;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node3(c4, c5, c6);
        return new Digit2(_c1, _c2);
      } else if (z->nchild == 3) {
        Digit3 *z_ = static_cast<Digit3 *>(z);
        Node *c5 = z_->c1;
        Node *c6 = z_->c2;
        Node *c7 = z_->c3;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node2(c4, c5);
        Node *_c3 = new Node2(c6, c7);
        return new Digit3(_c1, _c2, _c3);
      } else {
        Digit4 *z_ = static_cast<Digit4 *>(z);
        Node *c5 = z_->c1;
        Node *c6 = z_->c2;
        Node *c7 = z_->c3;
        Node *c8 = z_->c4;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node3(c4, c5, c6);
        Node *_c3 = new Node2(c7, c8);
        return new Digit3(_c1, _c2, _c3);
      }
    } else {
      Digit4 *y_ = static_cast<Digit4 *>(y);
      Node *c2 = y_->c1;
      Node *c3 = y_->c2;
      Node *c4 = y_->c3;
      Node *c5 = y_->c4;
      delete y_;
      if (z->nchild == 1) {
        Digit1 *z_ = static_cast<Digit1 *>(z);
        Node *c6 = z_->c1;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node3(c4, c5, c6);
        return new Digit2(_c1, _c2);
      } else if (z->nchild == 2) {
        Digit2 *z_ = static_cast<Digit2 *>(z);
        Node *c6 = z_->c1;
        Node *c7 = z_->c2;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node2(c4, c5);
        Node *_c3 = new Node2(c6, c7);
        return new Digit3(_c1, _c2, _c3);
      } else if (z->nchild == 3) {
        Digit3 *z_ = static_cast<Digit3 *>(z);
        Node *c6 = z_->c1;
        Node *c7 = z_->c2;
        Node *c8 = z_->c3;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node3(c4, c5, c6);
        Node *_c3 = new Node2(c7, c8);
        return new Digit3(_c1, _c2, _c3);
      } else {
        Digit4 *z_ = static_cast<Digit4 *>(z);
        Node *c6 = z_->c1;
        Node *c7 = z_->c2;
        Node *c8 = z_->c3;
        Node *c9 = z_->c4;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node3(c4, c5, c6);
        Node *_c3 = new Node3(c7, c8, c9);
        return new Digit3(_c1, _c2, _c3);
      }
    }
  } else if (x->nchild == 2) {
    Digit2 *x_ = static_cast<Digit2 *>(x);
    Node *c1 = x_->c1;
    Node *c2 = x_->c2;
    delete x_;
    if (y == nullptr) {
      if (z->nchild == 1) {
        Digit1 *z_ = static_cast<Digit1 *>(z);
        Node *c3 = z_->c1;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        return new Digit1(_c1);
      } else if (z->nchild == 2) {
        Digit2 *z_ = static_cast<Digit2 *>(z);
        Node *c3 = z_->c1;
        Node *c4 = z_->c2;
        delete z_;
        Node *_c1 = new Node2(c1, c2);
        Node *_c2 = new Node2(c3, c4);
        return new Digit2(_c1, _c2);
      } else if (z->nchild == 3) {
        Digit3 *z_ = static_cast<Digit3 *>(z);
        Node *c3 = z_->c1;
        Node *c4 = z_->c2;
        Node *c5 = z_->c3;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node2(c4, c5);
        return new Digit2(_c1, _c2);
      } else {
        Digit4 *z_ = static_cast<Digit4 *>(z);
        Node *c3 = z_->c1;
        Node *c4 = z_->c2;
        Node *c5 = z_->c3;
        Node *c6 = z_->c4;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node3(c4, c5, c6);
        return new Digit2(_c1, _c2);
      }
    } else if (y->nchild == 1) {
      Digit1 *y_ = static_cast<Digit1 *>(y);
      Node *c3 = y_->c1;
      delete y_;
      if (z->nchild == 1) {
        Digit1 *z_ = static_cast<Digit1 *>(z);
        Node *c4 = z_->c1;
        delete z_;
        Node *_c1 = new Node2(c1, c2);
        Node *_c2 = new Node2(c3, c4);
        return new Digit2(_c1, _c2);
      } else if (z->nchild == 2) {
        Digit2 *z_ = static_cast<Digit2 *>(z);
        Node *c4 = z_->c1;
        Node *c5 = z_->c2;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node2(c4, c5);
        return new Digit2(_c1, _c2);
      } else if (z->nchild == 3) {
        Digit3 *z_ = static_cast<Digit3 *>(z);
        Node *c4 = z_->c1;
        Node *c5 = z_->c2;
        Node *c6 = z_->c3;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node3(c4, c5, c6);
        return new Digit2(_c1, _c2);
      } else {
        Digit4 *z_ = static_cast<Digit4 *>(z);
        Node *c4 = z_->c1;
        Node *c5 = z_->c2;
        Node *c6 = z_->c3;
        Node *c7 = z_->c4;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node2(c4, c5);
        Node *_c3 = new Node2(c6, c7);
        return new Digit3(_c1, _c2, _c3);
      }
    } else if (y->nchild == 2) {
      Digit2 *y_ = static_cast<Digit2 *>(y);
      Node *c3 = y_->c1;
      Node *c4 = y_->c2;
      delete y_;
      if (z->nchild == 1) {
        Digit1 *z_ = static_cast<Digit1 *>(z);
        Node *c5 = z_->c1;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node2(c4, c5);
        return new Digit2(_c1, _c2);
      } else if (z->nchild == 2) {
        Digit2 *z_ = static_cast<Digit2 *>(z);
        Node *c5 = z_->c1;
        Node *c6 = z_->c2;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node3(c4, c5, c6);
        return new Digit2(_c1, _c2);
      } else if (z->nchild == 3) {
        Digit3 *z_ = static_cast<Digit3 *>(z);
        Node *c5 = z_->c1;
        Node *c6 = z_->c2;
        Node *c7 = z_->c3;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node2(c4, c5);
        Node *_c3 = new Node2(c6, c7);
        return new Digit3(_c1, _c2, _c3);
      } else {
        Digit4 *z_ = static_cast<Digit4 *>(z);
        Node *c5 = z_->c1;
        Node *c6 = z_->c2;
        Node *c7 = z_->c3;
        Node *c8 = z_->c4;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node3(c4, c5, c6);
        Node *_c3 = new Node2(c7, c8);
        return new Digit3(_c1, _c2, _c3);
      }
    } else if (y->nchild == 3) {
      Digit3 *y_ = static_cast<Digit3 *>(y);
      Node *c3 = y_->c1;
      Node *c4 = y_->c2;
      Node *c5 = y_->c3;
      delete y_;
      if (z->nchild == 1) {
        Digit1 *z_ = static_cast<Digit1 *>(z);
        Node *c6 = z_->c1;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node3(c4, c5, c6);
        return new Digit2(_c1, _c2);
      } else if (z->nchild == 2) {
        Digit2 *z_ = static_cast<Digit2 *>(z);
        Node *c6 = z_->c1;
        Node *c7 = z_->c2;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node2(c4, c5);
        Node *_c3 = new Node2(c6, c7);
        return new Digit3(_c1, _c2, _c3);
      } else if (z->nchild == 3) {
        Digit3 *z_ = static_cast<Digit3 *>(z);
        Node *c6 = z_->c1;
        Node *c7 = z_->c2;
        Node *c8 = z_->c3;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node3(c4, c5, c6);
        Node *_c3 = new Node2(c7, c8);
        return new Digit3(_c1, _c2, _c3);
      } else {
        Digit4 *z_ = static_cast<Digit4 *>(z);
        Node *c6 = z_->c1;
        Node *c7 = z_->c2;
        Node *c8 = z_->c3;
        Node *c9 = z_->c4;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node3(c4, c5, c6);
        Node *_c3 = new Node3(c7, c8, c9);
        return new Digit3(_c1, _c2, _c3);
      }
    } else {
      Digit4 *y_ = static_cast<Digit4 *>(y);
      Node *c3 = y_->c1;
      Node *c4 = y_->c2;
      Node *c5 = y_->c3;
      Node *c6 = y_->c4;
      delete y_;
      if (z->nchild == 1) {
        Digit1 *z_ = static_cast<Digit1 *>(z);
        Node *c7 = z_->c1;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node2(c4, c5);
        Node *_c3 = new Node2(c6, c7);
        return new Digit3(_c1, _c2, _c3);
      } else if (z->nchild == 2) {
        Digit2 *z_ = static_cast<Digit2 *>(z);
        Node *c7 = z_->c1;
        Node *c8 = z_->c2;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node3(c4, c5, c6);
        Node *_c3 = new Node2(c7, c8);
        return new Digit3(_c1, _c2, _c3);
      } else if (z->nchild == 3) {
        Digit3 *z_ = static_cast<Digit3 *>(z);
        Node *c7 = z_->c1;
        Node *c8 = z_->c2;
        Node *c9 = z_->c3;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node3(c4, c5, c6);
        Node *_c3 = new Node3(c7, c8, c9);
        return new Digit3(_c1, _c2, _c3);
      } else {
        Digit4 *z_ = static_cast<Digit4 *>(z);
        Node *c7 = z_->c1;
        Node *c8 = z_->c2;
        Node *c9 = z_->c3;
        Node *c10 = z_->c4;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node3(c4, c5, c6);
        Node *_c3 = new Node2(c7, c8);
        Node *_c4 = new Node2(c9, c10);
        return new Digit4(_c1, _c2, _c3, _c4);
      }
    }
  } else if (x->nchild == 3) {
    Digit3 *x_ = static_cast<Digit3 *>(x);
    Node *c1 = x_->c1;
    Node *c2 = x_->c2;
    Node *c3 = x_->c3;
    delete x_;
    if (y == nullptr) {
      if (z->nchild == 1) {
        Digit1 *z_ = static_cast<Digit1 *>(z);
        Node *c4 = z_->c1;
        delete z_;
        Node *_c1 = new Node2(c1, c2);
        Node *_c2 = new Node2(c3, c4);
        return new Digit2(_c1, _c2);
      } else if (z->nchild == 2) {
        Digit2 *z_ = static_cast<Digit2 *>(z);
        Node *c4 = z_->c1;
        Node *c5 = z_->c2;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node2(c4, c5);
        return new Digit2(_c1, _c2);
      } else if (z->nchild == 3) {
        Digit3 *z_ = static_cast<Digit3 *>(z);
        Node *c4 = z_->c1;
        Node *c5 = z_->c2;
        Node *c6 = z_->c3;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node3(c4, c5, c6);
        return new Digit2(_c1, _c2);
      } else {
        Digit4 *z_ = static_cast<Digit4 *>(z);
        Node *c4 = z_->c1;
        Node *c5 = z_->c2;
        Node *c6 = z_->c3;
        Node *c7 = z_->c4;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node2(c4, c5);
        Node *_c3 = new Node2(c6, c7);
        return new Digit3(_c1, _c2, _c3);
      }
    } else if (y->nchild == 1) {
      Digit1 *y_ = static_cast<Digit1 *>(y);
      Node *c4 = y_->c1;
      delete y_;
      if (z->nchild == 1) {
        Digit1 *z_ = static_cast<Digit1 *>(z);
        Node *c5 = z_->c1;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node2(c4, c5);
        return new Digit2(_c1, _c2);
      } else if (z->nchild == 2) {
        Digit2 *z_ = static_cast<Digit2 *>(z);
        Node *c5 = z_->c1;
        Node *c6 = z_->c2;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node3(c4, c5, c6);
        return new Digit2(_c1, _c2);
      } else if (z->nchild == 3) {
        Digit3 *z_ = static_cast<Digit3 *>(z);
        Node *c5 = z_->c1;
        Node *c6 = z_->c2;
        Node *c7 = z_->c3;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node2(c4, c5);
        Node *_c3 = new Node2(c6, c7);
        return new Digit3(_c1, _c2, _c3);
      } else {
        Digit4 *z_ = static_cast<Digit4 *>(z);
        Node *c5 = z_->c1;
        Node *c6 = z_->c2;
        Node *c7 = z_->c3;
        Node *c8 = z_->c4;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node3(c4, c5, c6);
        Node *_c3 = new Node2(c7, c8);
        return new Digit3(_c1, _c2, _c3);
      }
    } else if (y->nchild == 2) {
      Digit2 *y_ = static_cast<Digit2 *>(y);
      Node *c4 = y_->c1;
      Node *c5 = y_->c2;
      delete y_;
      if (z->nchild == 1) {
        Digit1 *z_ = static_cast<Digit1 *>(z);
        Node *c6 = z_->c1;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node3(c4, c5, c6);
        return new Digit2(_c1, _c2);
      } else if (z->nchild == 2) {
        Digit2 *z_ = static_cast<Digit2 *>(z);
        Node *c6 = z_->c1;
        Node *c7 = z_->c2;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node2(c4, c5);
        Node *_c3 = new Node2(c6, c7);
        return new Digit3(_c1, _c2, _c3);
      } else if (z->nchild == 3) {
        Digit3 *z_ = static_cast<Digit3 *>(z);
        Node *c6 = z_->c1;
        Node *c7 = z_->c2;
        Node *c8 = z_->c3;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node3(c4, c5, c6);
        Node *_c3 = new Node2(c7, c8);
        return new Digit3(_c1, _c2, _c3);
      } else {
        Digit4 *z_ = static_cast<Digit4 *>(z);
        Node *c6 = z_->c1;
        Node *c7 = z_->c2;
        Node *c8 = z_->c3;
        Node *c9 = z_->c4;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node3(c4, c5, c6);
        Node *_c3 = new Node3(c7, c8, c9);
        return new Digit3(_c1, _c2, _c3);
      }
    } else if (y->nchild == 3) {
      Digit3 *y_ = static_cast<Digit3 *>(y);
      Node *c4 = y_->c1;
      Node *c5 = y_->c2;
      Node *c6 = y_->c3;
      delete y_;
      if (z->nchild == 1) {
        Digit1 *z_ = static_cast<Digit1 *>(z);
        Node *c7 = z_->c1;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node2(c4, c5);
        Node *_c3 = new Node2(c6, c7);
        return new Digit3(_c1, _c2, _c3);
      } else if (z->nchild == 2) {
        Digit2 *z_ = static_cast<Digit2 *>(z);
        Node *c7 = z_->c1;
        Node *c8 = z_->c2;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node3(c4, c5, c6);
        Node *_c3 = new Node2(c7, c8);
        return new Digit3(_c1, _c2, _c3);
      } else if (z->nchild == 3) {
        Digit3 *z_ = static_cast<Digit3 *>(z);
        Node *c7 = z_->c1;
        Node *c8 = z_->c2;
        Node *c9 = z_->c3;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node3(c4, c5, c6);
        Node *_c3 = new Node3(c7, c8, c9);
        return new Digit3(_c1, _c2, _c3);
      } else {
        Digit4 *z_ = static_cast<Digit4 *>(z);
        Node *c7 = z_->c1;
        Node *c8 = z_->c2;
        Node *c9 = z_->c3;
        Node *c10 = z_->c4;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node3(c4, c5, c6);
        Node *_c3 = new Node2(c7, c8);
        Node *_c4 = new Node2(c9, c10);
        return new Digit4(_c1, _c2, _c3, _c4);
      }
    } else {
      Digit4 *y_ = static_cast<Digit4 *>(y);
      Node *c4 = y_->c1;
      Node *c5 = y_->c2;
      Node *c6 = y_->c3;
      Node *c7 = y_->c4;
      delete y_;
      if (z->nchild == 1) {
        Digit1 *z_ = static_cast<Digit1 *>(z);
        Node *c8 = z_->c1;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node3(c4, c5, c6);
        Node *_c3 = new Node2(c7, c8);
        return new Digit3(_c1, _c2, _c3);
      } else if (z->nchild == 2) {
        Digit2 *z_ = static_cast<Digit2 *>(z);
        Node *c8 = z_->c1;
        Node *c9 = z_->c2;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node3(c4, c5, c6);
        Node *_c3 = new Node3(c7, c8, c9);
        return new Digit3(_c1, _c2, _c3);
      } else if (z->nchild == 3) {
        Digit3 *z_ = static_cast<Digit3 *>(z);
        Node *c8 = z_->c1;
        Node *c9 = z_->c2;
        Node *c10 = z_->c3;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node3(c4, c5, c6);
        Node *_c3 = new Node2(c7, c8);
        Node *_c4 = new Node2(c9, c10);
        return new Digit4(_c1, _c2, _c3, _c4);
      } else {
        Digit4 *z_ = static_cast<Digit4 *>(z);
        Node *c8 = z_->c1;
        Node *c9 = z_->c2;
        Node *c10 = z_->c3;
        Node *c11 = z_->c4;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node3(c4, c5, c6);
        Node *_c3 = new Node3(c7, c8, c9);
        Node *_c4 = new Node2(c10, c11);
        return new Digit4(_c1, _c2, _c3, _c4);
      }
    }
  } else {
    Digit4 *x_ = static_cast<Digit4 *>(x);
    Node *c1 = x_->c1;
    Node *c2 = x_->c2;
    Node *c3 = x_->c3;
    Node *c4 = x_->c4;
    delete x_;
    if (y == nullptr) {
      if (z->nchild == 1) {
        Digit1 *z_ = static_cast<Digit1 *>(z);
        Node *c5 = z_->c1;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node2(c4, c5);
        return new Digit2(_c1, _c2);
      } else if (z->nchild == 2) {
        Digit2 *z_ = static_cast<Digit2 *>(z);
        Node *c5 = z_->c1;
        Node *c6 = z_->c2;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node3(c4, c5, c6);
        return new Digit2(_c1, _c2);
      } else if (z->nchild == 3) {
        Digit3 *z_ = static_cast<Digit3 *>(z);
        Node *c5 = z_->c1;
        Node *c6 = z_->c2;
        Node *c7 = z_->c3;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node2(c4, c5);
        Node *_c3 = new Node2(c6, c7);
        return new Digit3(_c1, _c2, _c3);
      } else {
        Digit4 *z_ = static_cast<Digit4 *>(z);
        Node *c5 = z_->c1;
        Node *c6 = z_->c2;
        Node *c7 = z_->c3;
        Node *c8 = z_->c4;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node3(c4, c5, c6);
        Node *_c3 = new Node2(c7, c8);
        return new Digit3(_c1, _c2, _c3);
      }
    } else if (y->nchild == 1) {
      Digit1 *y_ = static_cast<Digit1 *>(y);
      Node *c5 = y_->c1;
      delete y_;
      if (z->nchild == 1) {
        Digit1 *z_ = static_cast<Digit1 *>(z);
        Node *c6 = z_->c1;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node3(c4, c5, c6);
        return new Digit2(_c1, _c2);
      } else if (z->nchild == 2) {
        Digit2 *z_ = static_cast<Digit2 *>(z);
        Node *c6 = z_->c1;
        Node *c7 = z_->c2;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node2(c4, c5);
        Node *_c3 = new Node2(c6, c7);
        return new Digit3(_c1, _c2, _c3);
      } else if (z->nchild == 3) {
        Digit3 *z_ = static_cast<Digit3 *>(z);
        Node *c6 = z_->c1;
        Node *c7 = z_->c2;
        Node *c8 = z_->c3;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node3(c4, c5, c6);
        Node *_c3 = new Node2(c7, c8);
        return new Digit3(_c1, _c2, _c3);
      } else {
        Digit4 *z_ = static_cast<Digit4 *>(z);
        Node *c6 = z_->c1;
        Node *c7 = z_->c2;
        Node *c8 = z_->c3;
        Node *c9 = z_->c4;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node3(c4, c5, c6);
        Node *_c3 = new Node3(c7, c8, c9);
        return new Digit3(_c1, _c2, _c3);
      }
    } else if (y->nchild == 2) {
      Digit2 *y_ = static_cast<Digit2 *>(y);
      Node *c5 = y_->c1;
      Node *c6 = y_->c2;
      delete y_;
      if (z->nchild == 1) {
        Digit1 *z_ = static_cast<Digit1 *>(z);
        Node *c7 = z_->c1;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node2(c4, c5);
        Node *_c3 = new Node2(c6, c7);
        return new Digit3(_c1, _c2, _c3);
      } else if (z->nchild == 2) {
        Digit2 *z_ = static_cast<Digit2 *>(z);
        Node *c7 = z_->c1;
        Node *c8 = z_->c2;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node3(c4, c5, c6);
        Node *_c3 = new Node2(c7, c8);
        return new Digit3(_c1, _c2, _c3);
      } else if (z->nchild == 3) {
        Digit3 *z_ = static_cast<Digit3 *>(z);
        Node *c7 = z_->c1;
        Node *c8 = z_->c2;
        Node *c9 = z_->c3;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node3(c4, c5, c6);
        Node *_c3 = new Node3(c7, c8, c9);
        return new Digit3(_c1, _c2, _c3);
      } else {
        Digit4 *z_ = static_cast<Digit4 *>(z);
        Node *c7 = z_->c1;
        Node *c8 = z_->c2;
        Node *c9 = z_->c3;
        Node *c10 = z_->c4;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node3(c4, c5, c6);
        Node *_c3 = new Node2(c7, c8);
        Node *_c4 = new Node2(c9, c10);
        return new Digit4(_c1, _c2, _c3, _c4);
      }
    } else if (y->nchild == 3) {
      Digit3 *y_ = static_cast<Digit3 *>(y);
      Node *c5 = y_->c1;
      Node *c6 = y_->c2;
      Node *c7 = y_->c3;
      delete y_;
      if (z->nchild == 1) {
        Digit1 *z_ = static_cast<Digit1 *>(z);
        Node *c8 = z_->c1;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node3(c4, c5, c6);
        Node *_c3 = new Node2(c7, c8);
        return new Digit3(_c1, _c2, _c3);
      } else if (z->nchild == 2) {
        Digit2 *z_ = static_cast<Digit2 *>(z);
        Node *c8 = z_->c1;
        Node *c9 = z_->c2;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node3(c4, c5, c6);
        Node *_c3 = new Node3(c7, c8, c9);
        return new Digit3(_c1, _c2, _c3);
      } else if (z->nchild == 3) {
        Digit3 *z_ = static_cast<Digit3 *>(z);
        Node *c8 = z_->c1;
        Node *c9 = z_->c2;
        Node *c10 = z_->c3;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node3(c4, c5, c6);
        Node *_c3 = new Node2(c7, c8);
        Node *_c4 = new Node2(c9, c10);
        return new Digit4(_c1, _c2, _c3, _c4);
      } else {
        Digit4 *z_ = static_cast<Digit4 *>(z);
        Node *c8 = z_->c1;
        Node *c9 = z_->c2;
        Node *c10 = z_->c3;
        Node *c11 = z_->c4;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node3(c4, c5, c6);
        Node *_c3 = new Node3(c7, c8, c9);
        Node *_c4 = new Node2(c10, c11);
        return new Digit4(_c1, _c2, _c3, _c4);
      }
    } else {
      Digit4 *y_ = static_cast<Digit4 *>(y);
      Node *c5 = y_->c1;
      Node *c6 = y_->c2;
      Node *c7 = y_->c3;
      Node *c8 = y_->c4;
      delete y_;
      if (z->nchild == 1) {
        Digit1 *z_ = static_cast<Digit1 *>(z);
        Node *c9 = z_->c1;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node3(c4, c5, c6);
        Node *_c3 = new Node3(c7, c8, c9);
        return new Digit3(_c1, _c2, _c3);
      } else if (z->nchild == 2) {
        Digit2 *z_ = static_cast<Digit2 *>(z);
        Node *c9 = z_->c1;
        Node *c10 = z_->c2;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node3(c4, c5, c6);
        Node *_c3 = new Node2(c7, c8);
        Node *_c4 = new Node2(c9, c10);
        return new Digit4(_c1, _c2, _c3, _c4);
      } else if (z->nchild == 3) {
        Digit3 *z_ = static_cast<Digit3 *>(z);
        Node *c9 = z_->c1;
        Node *c10 = z_->c2;
        Node *c11 = z_->c3;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node3(c4, c5, c6);
        Node *_c3 = new Node3(c7, c8, c9);
        Node *_c4 = new Node2(c10, c11);
        return new Digit4(_c1, _c2, _c3, _c4);
      } else {
        Digit4 *z_ = static_cast<Digit4 *>(z);
        Node *c9 = z_->c1;
        Node *c10 = z_->c2;
        Node *c11 = z_->c3;
        Node *c12 = z_->c4;
        delete z_;
        Node *_c1 = new Node3(c1, c2, c3);
        Node *_c2 = new Node3(c4, c5, c6);
        Node *_c3 = new Node3(c7, c8, c9);
        Node *_c4 = new Node3(c10, c11, c12);
        return new Digit4(_c1, _c2, _c3, _c4);
      }
    }
  }
}

static inline Tree *pushDigitFront(Digit *ts, Tree *ys) {
  if (ts == nullptr) {
    return ys;
  } if (ts->nchild == 1) {
    Digit1 *dgt = static_cast<Digit1 *>(ts);
    Node *a = dgt->c1;
    delete dgt;
    return pushNodeFront(a, ys);
  } else if (ts->nchild == 2) {
    Digit2 *dgt = static_cast<Digit2 *>(ts);
    Node
      *a = dgt->c1,
      *b = dgt->c2;
    delete dgt;
    return pushNodeFront(a,
           pushNodeFront(b, ys));
  } else if (ts->nchild == 3) {
    Digit3 *dgt = static_cast<Digit3 *>(ts);
    Node
      *a = dgt->c1,
      *b = dgt->c2,
      *c = dgt->c3;
    delete dgt;
    return pushNodeFront(a,
           pushNodeFront(b,
           pushNodeFront(c, ys)));
  } else {
    Digit4 *dgt = static_cast<Digit4 *>(ts);
    Node
      *a = dgt->c1,
      *b = dgt->c2,
      *c = dgt->c3,
      *d = dgt->c4;
    delete dgt;
    return pushNodeFront(a,
           pushNodeFront(b,
           pushNodeFront(c,
           pushNodeFront(d, ys))));
  }
}

static inline Tree *pushDigitBack(Tree *xs, Digit *ts) {
  if (ts == nullptr) {
    return xs;
  } if (ts->nchild == 1) {
    Digit1 *dgt = static_cast<Digit1 *>(ts);
    Node *a = dgt->c1;
    delete dgt;
    return pushNodeBack(xs, a);
  } else if (ts->nchild == 2) {
    Digit2 *dgt = static_cast<Digit2 *>(ts);
    Node
      *a = dgt->c1,
      *b = dgt->c2;
    delete dgt;
    return pushNodeBack(pushNodeBack(xs, a), b);
  } else if (ts->nchild == 3) {
    Digit3 *dgt = static_cast<Digit3 *>(ts);
    Node
      *a = dgt->c1,
      *b = dgt->c2,
      *c = dgt->c3;
    delete dgt;
    return pushNodeBack(pushNodeBack(pushNodeBack(xs, a), b), c);
  } else {
    Digit4 *dgt = static_cast<Digit4 *>(ts);
    Node
      *a = dgt->c1,
      *b = dgt->c2,
      *c = dgt->c3,
      *d = dgt->c4;
    delete dgt;
    return pushNodeBack(pushNodeBack(pushNodeBack(pushNodeBack(xs, a), b), c), d);
  }
}

static Tree *app3(Tree *xs, Digit *ts, Tree *ys) {
  if (xs == nullptr) {
    return pushDigitFront(ts, ys);
  } else if (ys == nullptr) {
    return pushDigitBack(xs, ts);
  } else if (xs->single != nullptr) {
    Tree *zs = pushDigitFront(ts, ys);
    zs = pushNodeFront(xs->single, zs);
    delete xs;
    return zs;
  } else if (ys->single != nullptr) {
    Tree *zs = pushDigitBack(xs, ts);
    zs = pushNodeBack(zs, ys->single);
    delete ys;
    return zs;
  } else {
    xs->deep = app3(xs->deep,
                    digitsToDigit(xs->fingerr, ts, ys->fingerl),
                    ys->deep);
    xs->fingerr = ys->fingerr;
    xs->size = xs->fingerl->size + xs->deep->size + xs->fingerr->size;
    delete ys;
    return xs;
  }
}

static inline Tree *append(Tree *xs, Tree *ys) {
  return app3(xs, nullptr, ys);
}

static inline Node *splitDigitLeft(Digit *a, size_t pos, Tree *&l, Digit *&r) {
  if (a->nchild == 1) {
    Digit1 *dgt = static_cast<Digit1 *>(a);
    Node *a = dgt->c1;
    delete dgt;
    l = nullptr;
    r = nullptr;
    return a;
  } else if (a->nchild == 2) {
    Digit2 *dgt = static_cast<Digit2 *>(a);
    Node
      *a = dgt->c1,
      *b = dgt->c2;
    delete dgt;
    if (pos < a->size) {
      l = nullptr;
      r = new Digit1(b);
      return a;
    } else {
      l = new Tree(a);
      r = nullptr;
      return b;
    }
  } else if (a->nchild == 3) {
    Digit3 *dgt = static_cast<Digit3 *>(a);
    Node
      *a = dgt->c1,
      *b = dgt->c2,
      *c = dgt->c3;
    delete dgt;
    if (pos < a->size) {
      l = nullptr;
      r = new Digit2(b, c);
      return a;
    }
    pos -= a->size;
    if (pos < b->size) {
      l = new Tree(a);
      r = new Digit1(c);
      return b;
    } else {
      l = new Tree(new Digit1(a), nullptr, new Digit1(b));
      r = nullptr;
      return c;
    }
  } else {
    Digit4 *dgt = static_cast<Digit4 *>(a);
    Node
      *a = dgt->c1,
      *b = dgt->c2,
      *c = dgt->c3,
      *d = dgt->c4;
    delete dgt;
    if (pos < a->size) {
      l = nullptr;
      r = new Digit3(b, c, d);
      return a;
    }
    pos -= a->size;
    if (pos < b->size) {
      l = new Tree(a);
      r = new Digit2(c, d);
      return b;
    }
    pos -= b->size;
    if (pos < c->size) {
      l = new Tree(new Digit1(a), nullptr, new Digit1(b));
      r = new Digit1(d);
      return c;
    } else {
      l = new Tree(new Digit1(a), nullptr, new Digit2(b, c));
      r = nullptr;
      return d;
    }
  }
}

static inline Node *splitDigitRight(Digit *a, size_t pos, Digit *&l, Tree *&r) {
  if (a->nchild == 1) {
    Digit1 *dgt = static_cast<Digit1 *>(a);
    Node *a = dgt->c1;
    delete dgt;
    l = nullptr;
    r = nullptr;
    return a;
  } else if (a->nchild == 2) {
    Digit2 *dgt = static_cast<Digit2 *>(a);
    Node
      *a = dgt->c1,
      *b = dgt->c2;
    delete dgt;
    if (pos < a->size) {
      l = nullptr;
      r = new Tree(b);
      return a;
    } else {
      l = new Digit1(a);
      r = nullptr;
      return b;
    }
  } else if (a->nchild == 3) {
    Digit3 *dgt = static_cast<Digit3 *>(a);
    Node
      *a = dgt->c1,
      *b = dgt->c2,
      *c = dgt->c3;
    delete dgt;
    if (pos < a->size) {
      l = nullptr;
      r = new Tree(new Digit1(b), nullptr, new Digit1(c));
      return a;
    }
    pos -= a->size;
    if (pos < b->size) {
      l = new Digit1(a);
      r = new Tree(c);
      return b;
    } else {
      l = new Digit2(a, b);
      r = nullptr;
      return c;
    }
  } else {
    Digit4 *dgt = static_cast<Digit4 *>(a);
    Node
      *a = dgt->c1,
      *b = dgt->c2,
      *c = dgt->c3,
      *d = dgt->c4;
    delete dgt;
    if (pos < a->size) {
      l = nullptr;
      r = new Tree(new Digit1(b), nullptr, new Digit2(c, d));
      return a;
    }
    pos -= a->size;
    if (pos < b->size) {
      l = new Digit1(a);
      r = new Tree(new Digit1(c), nullptr, new Digit1(d));
      return b;
    }
    pos -= b->size;
    if (pos < c->size) {
      l = new Digit2(a, b);
      r = new Tree(d);
      return c;
    } else {
      l = new Digit3(a, b, c);
      r = nullptr;
      return d;
    }
  }
}

static inline Node *splitNode(Node *a, size_t pos, Digit *&l, Digit *&r) {
  if (a->nchild == 2) {
    Node2 *a2 = static_cast<Node2 *>(a);
    Node
      *a = a2->c1,
      *b = a2->c2;
    delete a2;
    if (pos < a->size) {
      l = nullptr;
      r = new Digit1(b);
      return a;
    } else {
      l = new Digit1(a);
      r = nullptr;
      return b;
    }
  } else {
    Node3 *a3 = static_cast<Node3 *>(a);
    Node
      *a = a3->c1,
      *b = a3->c2,
      *c = a3->c3;
    delete a3;
    if (pos < a->size) {
      l = nullptr;
      r = new Digit2(b, c);
      return a;
    }
    pos -= a->size;
    if (pos < b->size) {
      l = new Digit1(a);
      r = new Digit1(c);
      return b;
    } else {
      l = new Digit2(a, b);
      r = nullptr;
      return c;
    }
  }
}

static inline Tree *deepLeft(Tree *t) {
  if (t->fingerl == nullptr) {
    if (t->deep == nullptr) {
      return digitToTree(t, t->fingerr);
    } else {
      Node *h;
      t->deep = popNodeFront(h, t->deep);
      t->fingerl = nodeToDigit(h);
      return t;
    }
  } else {
    return t;
  }
}

static inline Tree *deepRight(Tree *t) {
  if (t->fingerr == nullptr) {
    if (t->deep == nullptr) {
      return digitToTree(t, t->fingerl);
    } else {
      Node *b;
      t->deep = popNodeBack(t->deep, b);
      t->fingerr = nodeToDigit(b);
      return t;
    }
  } else {
    return t;
  }
}

static inline void updateSize(Tree *t) {
  t->size = 0;
  if (t->fingerl != nullptr) {
    t->size += t->fingerl->size;
  }
  if (t->fingerr != nullptr) {
    t->size += t->fingerr->size;
  }
  if (t->deep != nullptr) {
    t->size += t->deep->size;
  }
}

// [0, pos) , pos, [pos + 1, size)
static Node *split(Tree *t, size_t pos, Tree *&l, Tree *&r) {
  if (t->single != nullptr) {
    l = r = nullptr;
    Node *a = t->single;
    delete t;
    return a;
  } else {
    if (pos < t->fingerl->size) {
      Node *ret = splitDigitLeft(t->fingerl, pos, l, t->fingerl);
      updateSize(t);
      r = deepLeft(t);
      return ret;
    }
    pos -= t->fingerl->size;
    if (t->deep == nullptr || pos >= t->deep->size) {
      pos -= (t->deep == nullptr ? 0 : t->deep->size);
      Node *ret = splitDigitRight(t->fingerr, pos, t->fingerr, r);
      updateSize(t);
      l = deepRight(t);
      return ret;
    } else {
      Tree *ml, *mr;
      Node *ret = split(t->deep, pos, ml, mr);
      Digit *lr, *rl;
      if (ml != nullptr) {
        pos -= ml->size;
      }
      ret = splitNode(ret, pos, lr, rl);
      t->deep = mr;
      l = deepRight(new Tree(t->fingerl, ml, lr));
      t->fingerl = rl;
      updateSize(t);
      r = deepLeft(t);
      return ret;
    }
  }
}

template<class Data>
static inline Node *headDigit(Digit *a) {
  if (a->nchild == 1) {
    return static_cast<Digit1 *>(a)->c1;
  } else if (a->nchild == 2) {
    return static_cast<Digit2 *>(a)->c1;
  } else if (a->nchild == 3) {
    return static_cast<Digit3 *>(a)->c1;
  } else {
    return static_cast<Digit4 *>(a)->c1;
  }
}

template<class Data>
static inline Data &head(Tree *t) {
  if (t->single != nullptr) {
    return static_cast<Leaf<Data> *>(t->single)->data;
  } else {
    return static_cast<Leaf<Data> *>(headDigit<Data>(t->fingerl))->data;
  }
}

template<class Data>
static inline Node *lastDigit(Digit *a) {
  if (a->nchild == 1) {
    return static_cast<Digit1 *>(a)->c1;
  } else if (a->nchild == 2) {
    return static_cast<Digit2 *>(a)->c2;
  } else if (a->nchild == 3) {
    return static_cast<Digit3 *>(a)->c3;
  } else {
    return static_cast<Digit4 *>(a)->c4;
  }
}

template<class Data>
static inline Data &last(Tree *t) {
  if (t->single != nullptr) {
    return static_cast<Leaf<Data> *>(t->single)->data;
  } else {
    return static_cast<Leaf<Data> *>(lastDigit<Data>(t->fingerr))->data;
  }
}

template<class Data>
static Node *copyNode(Node *a) {
  if (a->nchild == 2) {
    Node2 *a2 = static_cast<Node2 *>(a);
    return new Node2(copyNode<Data>(a2->c1),
                     copyNode<Data>(a2->c2));
  } else if (a->nchild == 3) {
    Node3 *a3 = static_cast<Node3 *>(a);
    return new Node3(copyNode<Data>(a3->c1),
                     copyNode<Data>(a3->c2),
                     copyNode<Data>(a3->c3));
  } else {
    return new Leaf<Data>(static_cast<Leaf<Data> *>(a)->data);
  }
}

template<class Data>
static inline Digit *copyDigit(Digit *a) {
  if (a->nchild == 1) {
    return new Digit1(copyNode<Data>(static_cast<Digit1 *>(a)->c1));
  } else if (a->nchild == 2) {
    Digit2 *dgt = static_cast<Digit2 *>(a);
    return new Digit2(copyNode<Data>(dgt->c1),
                      copyNode<Data>(dgt->c2));
  } else if (a->nchild == 3) {
    Digit3 *dgt = static_cast<Digit3 *>(a);
    return new Digit3(copyNode<Data>(dgt->c1),
                      copyNode<Data>(dgt->c2),
                      copyNode<Data>(dgt->c3));
  } else {
    Digit4 *dgt = static_cast<Digit4 *>(a);
    return new Digit4(copyNode<Data>(dgt->c1),
                      copyNode<Data>(dgt->c2),
                      copyNode<Data>(dgt->c3),
                      copyNode<Data>(dgt->c4));
  }
}

template<class Data>
static inline Tree *copy(Tree *t) {
  if (t == nullptr) {
    return nullptr;
  } else if (t->single != nullptr) {
    return new Tree(copyNode<Data>(t->single));
  } else {
    return new Tree(copyDigit<Data>(t->fingerl),
                    copy<Data>(t->deep),
                    copyDigit<Data>(t->fingerr));
  }
}

template<class Data>
static void freeNode(Node *a) {
  if (a->nchild == 2) {
    Node2 *a2 = static_cast<Node2 *>(a);
    freeNode<Data>(a2->c1);
    freeNode<Data>(a2->c2);
    delete a2;
  } else if (a->nchild == 3) {
    Node3 *a3 = static_cast<Node3 *>(a);
    freeNode<Data>(a3->c1);
    freeNode<Data>(a3->c2);
    freeNode<Data>(a3->c3);
    delete a3;
  } else {
    delete static_cast<Leaf<Data> *>(a);
  }
}

template<class Data>
static inline void freeDigit(Digit *a) {
  if (a->nchild == 1) {
    freeNode<Data>(static_cast<Digit1 *>(a)->c1);
  } else if (a->nchild == 2) {
    Digit2 *dgt = static_cast<Digit2 *>(a);
    freeNode<Data>(dgt->c1);
    freeNode<Data>(dgt->c2);
  } else if (a->nchild == 3) {
    Digit3 *dgt = static_cast<Digit3 *>(a);
    freeNode<Data>(dgt->c1);
    freeNode<Data>(dgt->c2);
    freeNode<Data>(dgt->c3);
  } else if (a->nchild == 4) {
    Digit4 *dgt = static_cast<Digit4 *>(a);
    freeNode<Data>(dgt->c1);
    freeNode<Data>(dgt->c2);
    freeNode<Data>(dgt->c3);
    freeNode<Data>(dgt->c4);
  }
  delete a;
}

template<class Data>
static void freeTree(Tree *t) {
  if (t == nullptr) {
    return;
  } else if (t->single != nullptr) {
    freeNode<Data>(t->single);
    delete t;
  } else {
    freeDigit<Data>(t->fingerl);
    freeTree<Data>(t->deep);
    freeDigit<Data>(t->fingerr);
    delete t;
  }
}

template <class Data>
class deque {
private:
  Tree *root;
public:
  class const_iterator;
  class iterator {
    friend class deque;
    friend class const_iterator;
  private:
    deque *iteratee;
    size_t pos;
    iterator(deque *iteratee, size_t pos)
      : iteratee(iteratee), pos(pos) {}
  public:
    iterator() = default;

    iterator operator+(const int &n) const {
      iterator temp = *this;
      return (temp += n);
    }

    iterator operator-(const int &n) const {
      iterator temp = *this;
      return (temp -= n);
    }

    int operator-(const iterator &rhs) const {
      if (rhs.iteratee != iteratee) {
        throw "invalid iterator";
      } else {
        return static_cast<int>(pos - rhs.pos);
      }
    }

    iterator &operator+=(const int &n) {
      if (n < 0) {
        return (*this -= (-n));
      }
      pos += n;
      if (pos > iteratee->size()) {
        throw "invalid iterator";
      }
      return *this;
    }

    iterator &operator-=(const int &n) {
      if (n < 0) {
        return (*this += (-n));
      }
      if (pos < n) {
        throw "invalid iterator";
      }
      pos -= n;
      return *this;
    }

    iterator operator++(int) {
      iterator temp = *this;
      *this += 1;
      return temp;
    }

    iterator &operator++() { return (*this += 1); }

    iterator operator--(int) {
      iterator temp = *this;
      *this -= 1;
      return temp;
    }

    iterator &operator--() { return (*this -= 1); }

    Data &operator*() const {
      if (pos == iteratee->size())
        throw "invalid iterator";
      return iteratee->at(pos);
    }

    Data *operator->() const noexcept {
      if (pos == iteratee->size()) {
        return nullptr;
      } else {
        return &iteratee->at(pos);
      }
    }

    bool operator==(const iterator &rhs) const {
      return iteratee == rhs.iteratee && pos == rhs.pos;
    }

    bool operator==(const const_iterator &rhs) const {
      return iteratee == rhs.iteratee && pos == rhs.pos;
    }

    bool operator!=(const iterator &rhs) const { return !(*this == rhs); }

    bool operator!=(const const_iterator &rhs) const { return !(*this == rhs); }
  };

  class const_iterator {
    friend class iterator;
    friend class deque;
  private:
    const deque *iteratee;
    size_t pos;
    const_iterator(const deque *iteratee, size_t pos)
        : iteratee(iteratee), pos(pos) {}
  public:
    const_iterator() = default;
    const_iterator operator+(const int &n) const {
      const_iterator temp = *this;
      return (temp += n);
    }

    const_iterator operator-(const int &n) const {
      const_iterator temp = *this;
      return (temp -= n);
    }

    int operator-(const const_iterator &rhs) const {
      if (rhs.iteratee != iteratee) {
        throw "invalid iterator";
      } else {
        return static_cast<int>(pos - rhs.pos);
      }
    }

    const_iterator &operator+=(const int &n) {
      if (n < 0) {
        return (*this -= (-n));
      }
      pos += n;
      if (pos > iteratee->size()) {
        throw "invalid iterator";
      }
      return *this;
    }

    const_iterator &operator-=(const int &n) {
      if (n < 0) {
        return (*this += (-n));
      }
      if (pos < n) {
        throw "invalid iterator";
      }
      pos -= n;
      return *this;
    }

    const_iterator operator++(int) {
      const_iterator temp = *this;
      *this += 1;
      return temp;
    }

    const_iterator &operator++() { return (*this += 1); }

    const_iterator operator--(int) {
      const_iterator temp = *this;
      *this -= 1;
      return temp;
    }

    const_iterator &operator--() { return (*this -= 1); }

    const Data &operator*() const {
      if (pos == iteratee->size())
        throw "invalid iterator";
      return iteratee->at(pos);
    }

    const Data *operator->() const noexcept {
      if (pos == iteratee->size()) {
        return nullptr;
      } else {
        return &iteratee->at(pos);
      }
    }

    bool operator==(const iterator &rhs) const {
      return iteratee == rhs.iteratee && pos == rhs.pos;
    }

    bool operator==(const const_iterator &rhs) const {
      return iteratee == rhs.iteratee && pos == rhs.pos;
    }

    bool operator!=(const iterator &rhs) const { return !(*this == rhs); }

    bool operator!=(const const_iterator &rhs) const { return !(*this == rhs); }
  };

  friend class iterator;
  friend class const_iterator;

  deque() : root(nullptr) {}
  deque(const deque &other) : root(copy<Data>(other.root)) {}
  ~deque() {
    freeTree<Data>(root);
    root = nullptr;
  }
  deque &operator=(const deque &other) {
    if (&other != this) {
      freeTree<Data>(root);
      root = copy<Data>(other.root);
    }
    return *this;
  }

  size_t size() const {
    if (root == nullptr) {
      return 0;
    } else {
      return root->size;
    }
  }
  
  Data &at(const size_t &pos) {
    if (pos >= size()) {
      throw "index out of bound";
    } else {
      return ::at<Data>(root, pos);
    }
  }

  const Data &at(const size_t &pos) const {
    if (pos >= size()) {
      throw "index out of bound";
    } else {
      return ::at<Data>(root, pos);
    }
  }

  Data &operator[](const size_t &pos) { return at(pos); }

  const Data &operator[](const size_t &pos) const { return at(pos); }

  const Data &front() const {
    if (root == nullptr) {
      throw "container is empty";
    } else {
      return head<Data>(root);
    }
  }

  const Data &back() const {
    if (root == nullptr) {
      throw "container is empty";
    } else {
      return last<Data>(root);
    }
  }

  iterator begin() {
    return iterator(this, 0);
  }
  const_iterator cbegin() const {
    return const_iterator(this, 0);
  }
  iterator end() {
    return iterator(this, size());
  }
  const_iterator cend() const {
    return const_iterator(this, size());
  }

  bool empty() const {
    return root == nullptr;
  }

  void clear() {
    freeTree<Data>(root);
    root = nullptr;
  }

  iterator insert(iterator pos, const Data &v) {
    if (pos.iteratee != this) {
      throw "invalid iterator";
    } else if (pos.pos == size()) {
      push_back(v);
      return pos;
    } else {
      Tree *l, *r;
      Node *atpos = split(root, pos.pos, l, r);
      root = app3(l, new Digit2(new Leaf<Data>(v), atpos), r);
      return pos;
    }
  }

  iterator erase(iterator pos) {
    if (pos.iteratee != this || pos.pos == size()) {
      throw "invalid iterator";
    }
    Tree *l, *r;
    Node *atpos = split(root, pos.pos, l, r);
    delete static_cast<Leaf<Data> *>(atpos);
    root = append(l, r);
    return pos;
  }

  void push_back(const Data &value) {
    root = pushBack(root, value);
  }

  void pop_back() {
    root = popBack<Data>(root);
  }

  void push_front(const Data &value) {
    root = pushFront(value, root);
  }

  void pop_front() {
    root = popFront<Data>(root);
  }
};

