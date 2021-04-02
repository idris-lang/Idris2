test00 : {0 p : _} -> (1 v : (x : a 0|0 p x)) -> ()
test00 (x 0|0 y) = ?h00

test01 : {0 p : _} -> (1 v : (x : a 0|1 p x)) -> ()
test01 (x 0|1 y) = ?h01

test0W : {0 p : _} -> (1 v : (x : a 0|* p x)) -> ()
test0W (x 0|* y) = ?h0W

test10 : {0 p : _} -> (1 v : (x : a 1|0 p x)) -> ()
test10 (x 1|0 y) = ?h10

test11 : {0 p : _} -> (1 v : (x : a 1|1 p x)) -> ()
test11 (x 1|1 y) = ?h11

test1W : {0 p : _} -> (1 v : (x : a 1|* p x)) -> ()
test1W (x 1|* y) = ?h1W

testW0 : {0 p : _} -> (1 v : (x : a *|0 p x)) -> ()
testW0 (x *|0 y) = ?hW0

testW1 : {0 p : _} -> (1 v : (x : a *|1 p x)) -> ()
testW1 (x *|1 y) = ?hW1

testWW : {0 p : _} -> (1 v : (x : a *|* p x)) -> ()
testWW (x *|* y) = ?hWW

testWW' : {0 p : _} -> (1 v : (x : a ** p x)) -> ()
testWW' (x ** y) = ?hWW'

actuallyCanMatch : {0 p : a -> Type}
                -> (1 val : b)
                -> (0 v : (x *|1 p x))
                -> ()
actuallyCanMatch val (x *|1 y) = ?h10W1

||| Issue #499
test10W1 : {0 p : _} -> (1 v : (x : a 1|0 y : b *|1 p x y)) -> ()
test10W1 (x 1|0 cantMatchOnErased) = actuallyCanMatch x cantMatchOnErased

test11W1 : {0 p : _} -> (1 v : (x : a 1|1 y : b *|1 p x y)) -> ()
test11W1 (x 1|1 y *|1 z) = ?h11W1

test1W11 : {0 p : _} -> (1 v : (x : a 1|* y : b 1|1 p x y)) -> ()
test1W11 (x 1|* y 1|1 z) = ?h1W11


atest00 : {0 p : _} -> (0 x : a) -> (0 y : p x) -> (x : a 0|0 p x)
atest00 x y = (x 0|0 y)

atest01 : {0 p : _} -> (0 x : a) -> (1 y : p x) -> (x : a 0|1 p x)
atest01 x y = (x 0|1 y)

atest0W : {0 p : _} -> (0 x : a) -> (y : p x) -> (x : a 0|* p x)
atest0W x y = (x 0|* y)

atest10 : {0 p : _} -> (1 x : a) -> (0 y : p x) -> (x : a 1|0 p x)
atest10 x y = (x 1|0 y)

atest11 : {0 p : _} -> (1 x : a) -> (1 y : p x) -> (x : a 1|1 p x)
atest11 x y = (x 1|1 y)

atest1W : {0 p : _} -> (1 x : a) -> (y : p x) -> (x : a 1|* p x)
atest1W x y = (x 1|* y)

atestW0 : {0 p : _} -> (x : a) -> (0 y : p x) -> (x : a *|0 p x)
atestW0 x y = (x *|0 y)

atestW1 : {0 p : _} -> (x : a) -> (1 y : p x) -> (x : a *|1 p x)
atestW1 x y = (x *|1 y)

atestWW : {0 p : _} -> (x : a) -> (y : p x) -> (x : a *|* p x)
atestWW x y = (x *|* y)

atestWW' : {0 p : _} -> (x : a) -> (y : p x) -> (x : a ** p x)
atestWW' x y = (x ** y)

atest10W1 : {0 p : _} -> (1 x : a) -> (0 y : b) -> (0 z : p x y) -> (x : a 1|0 y : b *|1 p x y)
atest10W1 x y z = (x 1|0 y *|1 z)

