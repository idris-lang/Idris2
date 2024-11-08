export class IdrisError extends Error { }

export function __lazy(thunk) {
  let res;
  return function () {
    if (thunk === undefined) return res;
    res = thunk();
    thunk = undefined;
    return res;
  };
};

export function __prim_stringIteratorNew(_str) {
  return 0
}

export function __prim_stringIteratorToString(_, str, it, f) {
  return f(str.slice(it))
}

export function __prim_stringIteratorNext(str, it) {
  if (it >= str.length)
    return { h: 0 };
  else
    return { a1: str.charAt(it), a2: it + 1 };
}

export function __tailRec(f, ini) {
  let obj = ini;
  while (true) {
    switch (obj.h) {
      case 0: return obj.a1;
      default: obj = f(obj);
    }
  }
}

export const _idrisworld = Symbol('idrisworld')

export const _crashExp = x => { throw new IdrisError(x) }

export const _bigIntOfString = s => {
  try {
    const idx = s.indexOf('.')
    return idx === -1 ? BigInt(s) : BigInt(s.slice(0, idx))
  } catch (_e) { return 0n }
}

export const _numberOfString = s => {
  try {
    const res = Number(s);
    return isNaN(res) ? 0 : res;
  } catch (_e) { return 0 }
}

export const _intOfString = s => Math.trunc(_numberOfString(s))

export const _truncToChar = x => String.fromCodePoint(
  (x >= 0 && x <= 55295) || (x >= 57344 && x <= 1114111) ? x : 0
)

// Int8
export const _truncInt8 = x => {
  const res = x & 0xff;
  return res >= 0x80 ? res - 0x100 : res;
}

export const _truncBigInt8 = x => Number(BigInt.asIntN(8, x))

// Euclidian Division
export const _div = (a, b) => {
  const q = Math.trunc(a / b)
  const r = a % b
  return r < 0 ? (b > 0 ? q - 1 : q + 1) : q
}

export const _divBigInt = (a, b) => {
  const q = a / b
  const r = a % b
  return r < 0n ? (b > 0n ? q - 1n : q + 1n) : q
}

// Euclidian Modulo
export const _mod = (a, b) => {
  const r = a % b
  return r < 0 ? (b > 0 ? r + b : r - b) : r
}

export const _modBigInt = (a, b) => {
  const r = a % b
  return r < 0n ? (b > 0n ? r + b : r - b) : r
}

export const _add8s = (a, b) => _truncInt8(a + b)
export const _sub8s = (a, b) => _truncInt8(a - b)
export const _mul8s = (a, b) => _truncInt8(a * b)
export const _div8s = (a, b) => _truncInt8(_div(a, b))
export const _shl8s = (a, b) => _truncInt8(a << b)
export const _shr8s = (a, b) => _truncInt8(a >> b)

// Int16
export const _truncInt16 = x => {
  const res = x & 0xffff;
  return res >= 0x8000 ? res - 0x10000 : res;
}

export const _truncBigInt16 = x => Number(BigInt.asIntN(16, x))

export const _add16s = (a, b) => _truncInt16(a + b)
export const _sub16s = (a, b) => _truncInt16(a - b)
export const _mul16s = (a, b) => _truncInt16(a * b)
export const _div16s = (a, b) => _truncInt16(_div(a, b))
export const _shl16s = (a, b) => _truncInt16(a << b)
export const _shr16s = (a, b) => _truncInt16(a >> b)

//Int32
export const _truncInt32 = x => x & 0xffffffff

export const _truncBigInt32 = x => Number(BigInt.asIntN(32, x))

export const _add32s = (a, b) => _truncInt32(a + b)
export const _sub32s = (a, b) => _truncInt32(a - b)
export const _div32s = (a, b) => _truncInt32(_div(a, b))

export const _mul32s = (a, b) => {
  const res = a * b;
  if (res <= Number.MIN_SAFE_INTEGER || res >= Number.MAX_SAFE_INTEGER) {
    return _truncInt32((a & 0xffff) * b + (b & 0xffff) * (a & 0xffff0000))
  } else {
    return _truncInt32(res)
  }
}

//Int64
export const _truncBigInt64 = x => BigInt.asIntN(64, x)

export const _add64s = (a, b) => _truncBigInt64(a + b)
export const _sub64s = (a, b) => _truncBigInt64(a - b)
export const _mul64s = (a, b) => _truncBigInt64(a * b)
export const _shl64s = (a, b) => _truncBigInt64(a << b)
export const _div64s = (a, b) => _truncBigInt64(_divBigInt(a, b))
export const _shr64s = (a, b) => _truncBigInt64(a >> b)

//Bits8
export const _truncUInt8 = x => x & 0xff

export const _truncUBigInt8 = x => Number(BigInt.asUintN(8, x))

export const _add8u = (a, b) => (a + b) & 0xff
export const _sub8u = (a, b) => (a - b) & 0xff
export const _mul8u = (a, b) => (a * b) & 0xff
export const _div8u = (a, b) => Math.trunc(a / b)
export const _shl8u = (a, b) => (a << b) & 0xff
export const _shr8u = (a, b) => (a >> b) & 0xff

//Bits16
export const _truncUInt16 = x => x & 0xffff

export const _truncUBigInt16 = x => Number(BigInt.asUintN(16, x))

export const _add16u = (a, b) => (a + b) & 0xffff
export const _sub16u = (a, b) => (a - b) & 0xffff
export const _mul16u = (a, b) => (a * b) & 0xffff
export const _div16u = (a, b) => Math.trunc(a / b)
export const _shl16u = (a, b) => (a << b) & 0xffff
export const _shr16u = (a, b) => (a >> b) & 0xffff

//Bits32
export const _truncUBigInt32 = x => Number(BigInt.asUintN(32, x))

export const _truncUInt32 = x => {
  const res = x & -1;
  return res < 0 ? res + 0x100000000 : res;
}

export const _add32u = (a, b) => _truncUInt32(a + b)
export const _sub32u = (a, b) => _truncUInt32(a - b)
export const _mul32u = (a, b) => _truncUInt32(_mul32s(a, b))
export const _div32u = (a, b) => Math.trunc(a / b)

export const _shl32u = (a, b) => _truncUInt32(a << b)
export const _shr32u = (a, b) => _truncUInt32(a <= 0x7fffffff ? a >> b : (b == 0 ? a : (a >> b) ^ ((-0x80000000) >> (b - 1))))
export const _and32u = (a, b) => _truncUInt32(a & b)
export const _or32u = (a, b) => _truncUInt32(a | b)
export const _xor32u = (a, b) => _truncUInt32(a ^ b)

//Bits64
export const _truncUBigInt64 = x => BigInt.asUintN(64, x)

export const _add64u = (a, b) => BigInt.asUintN(64, a + b)
export const _mul64u = (a, b) => BigInt.asUintN(64, a * b)
export const _div64u = (a, b) => a / b
export const _shl64u = (a, b) => BigInt.asUintN(64, a << b)
export const _shr64u = (a, b) => BigInt.asUintN(64, a >> b)
export const _sub64u = (a, b) => BigInt.asUintN(64, a - b)

//String
export const _strReverse = x => x.split('').reverse().join('')

export const _substr = (o, l, x) => x.slice(o, o + l)
