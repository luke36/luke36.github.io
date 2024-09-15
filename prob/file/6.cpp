#include <iostream>
#include <vector>

using namespace std;

struct Dual {
  float p;
  Dual(float p): p(p) {}
  virtual void grad(float z) = 0;
};

struct Var: public Dual {
  float *loc;
  Var (float f): Dual(f), loc(nullptr) {}
  Var (float f, float *x): Dual(f), loc(x) {}
  virtual void grad(float z) {
    if (loc != nullptr)
      *loc += z;
  }
};

struct Plus: public Dual {
  Dual *a;
  Dual *b;
  Plus (Dual *a, Dual *b): Dual(a->p + b->p), a(a), b(b) {}
  virtual void grad(float z) {
    a->grad(z);
    b->grad(z);
  }
};

struct Mult: public Dual {
  Dual *a;
  Dual *b;
  Mult (Dual *a, Dual *b): Dual(a->p * b->p), a(a), b(b) {}
  virtual void grad(float z) {
    a->grad(z * b->p);
    b->grad(z * a->p);
  }
};

struct Wrap {
  struct Dual *d;
  Wrap (float f): d(new Var(f)) {}
  Wrap (Dual *d): d(d) {}
};

Wrap operator+(Wrap a, Wrap b) {
  return Wrap(new Plus(a.d, b.d));
}

Wrap operator*(Wrap a, Wrap b) {
  return Wrap(new Mult(a.d, b.d));
}

vector<float> gradient(Wrap (*f)(vector<Wrap> &), vector<float> &args) {
  vector<Wrap> v;
  vector<float> res(args.size());
  for (int i = 0; i < args.size(); i++)
    v.emplace_back(new Var(args[i], &res[i]));
  Wrap d = f(v);
  d.d->grad(1.0);
  return res;
}

template <typename T>
T f(vector<T> &args) {
  T x = args[0];
  T y = args[1];
  T z = x * x + x * (y + 1);
  return z;
}

int main() {
  float x = 1.0;
  float y = 1.0;
  vector<float> args = { x, y };
  vector<float> grad = gradient(f<Wrap>, args);
  cout << grad[0] << ' ' << grad[1];
}

