total
foo : (x, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16 : a) -> Nat
foo x a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
  = foo a0 x  a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
  + foo a1 a0 x  a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
  + foo a2 a0 a1 x  a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
  + foo a3 a0 a1 a2 x  a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
  + foo a4 a0 a1 a2 a3 x  a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
  + foo a5 a0 a1 a2 a3 a4 x  a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
  + foo a6 a0 a1 a2 a3 a4 a5 x  a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
  + foo a7 a0 a1 a2 a3 a4 a5 a6 x  a8 a9 a10 a11 a12 a13 a14 a15 a16
  + foo a8 a0 a1 a2 a3 a4 a5 a6 a7 x  a9 a10 a11 a12 a13 a14 a15 a16
  + foo a9 a0 a1 a2 a3 a4 a5 a6 a7 a8 x  a10 a11 a12 a13 a14 a15 a16
  + foo a10 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 x  a11 a12 a13 a14 a15 a16
  + foo a11 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 x  a12 a13 a14 a15 a16
  + foo a12 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 x  a13 a14 a15 a16
  + foo a13 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 x  a14 a15 a16
  + foo a14 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 x  a15 a16
  + foo a15 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 x  a16
  + foo a16 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 x
