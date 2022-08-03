module Libraries.Data.ControlFlow

%default total

||| Data structure made especially for loop control
||| Never forget what "True" means again!
public export
data ControlFlow c b = Continue c | Break b

||| Probably what you need instead of `Bool`
public export
ControlFlowUnit : Type
ControlFlowUnit = ControlFlow Unit Unit
