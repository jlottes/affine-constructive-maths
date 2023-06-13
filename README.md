# affine-constructive-maths
A library of constructive mathematics using affine logic, following Michael Shulman's "Affine logic for constructive mathematics."[^1], and heavily inspired by the [MathClasses library](https://github.com/coq-community/math-classes).

# Building

Compiles with Coq 8.17.0. To build:
```
git clone https://github.com/jlottes/affine-constructive-maths.git
cd affine-constructive-maths
coq_makefile -f _CoqProject -o Makefile
make
```

[^1]: Shulman, Michael. "Affine logic for constructive mathematics." Bulletin of Symbolic Logic 28.3 (2022): 327-386.
