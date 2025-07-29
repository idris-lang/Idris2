export const __prim_stringIteratorNew = _str => 0

export function __prim_stringIteratorToString(_, str, it, f) {
  return f(str.slice(it))
}

export function __prim_stringIteratorNext(str, it) {
  if (it >= str.length)
    return { h: 0 };
  else
    return { a1: str.charAt(it), a2: it + 1 };
}
