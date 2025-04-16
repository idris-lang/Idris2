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

export function __tailRec(f, ini) {
  let obj = ini;
  while (true) {
    switch (obj.h) {
      case 0: return obj.a1;
      default: obj = f(obj);
    }
  }
}

export const idrisworld = Symbol('idrisworld')

export const crashExp = x => { throw new IdrisError(x) }

export const bigIntOfString = s => {
  try {
    const idx = s.indexOf('.')
    return idx === -1 ? BigInt(s) : BigInt(s.slice(0, idx))
  } catch (_e) { return 0n }
}

export const numberOfString = s => {
  try {
    const res = Number(s);
    return isNaN(res) ? 0 : res;
  } catch (_e) { return 0 }
}

export const intOfString = s => Math.trunc(numberOfString(s))

export const truncToChar = x => String.fromCodePoint(
  (x >= 0 && x <= 55295) || (x >= 57344 && x <= 1114111) ? x : 0
)

// Int8
export const truncInt8 = x => {
  const res = x & 0xff;
  return res >= 0x80 ? res - 0x100 : res;
}

export const truncBigInt8 = x => Number(BigInt.asIntN(8, x))

// Euclidian Division
export const div = (a, b) => {
  const q = Math.trunc(a / b)
  const r = a % b
  return r < 0 ? (b > 0 ? q - 1 : q + 1) : q
}

export const divBigInt = (a, b) => {
  const q = a / b
  const r = a % b
  return r < 0n ? (b > 0n ? q - 1n : q + 1n) : q
}

// Euclidian Modulo
export const mod = (a, b) => {
  const r = a % b
  return r < 0 ? (b > 0 ? r + b : r - b) : r
}

export const modBigInt = (a, b) => {
  const r = a % b
  return r < 0n ? (b > 0n ? r + b : r - b) : r
}

export const add8s = (a, b) => truncInt8(a + b)
export const sub8s = (a, b) => truncInt8(a - b)
export const mul8s = (a, b) => truncInt8(a * b)
export const div8s = (a, b) => truncInt8(div(a, b))
export const shl8s = (a, b) => truncInt8(a << b)
export const shr8s = (a, b) => truncInt8(a >> b)

// Int16
export const truncInt16 = x => {
  const res = x & 0xffff;
  return res >= 0x8000 ? res - 0x10000 : res;
}

export const truncBigInt16 = x => Number(BigInt.asIntN(16, x))

export const add16s = (a, b) => truncInt16(a + b)
export const sub16s = (a, b) => truncInt16(a - b)
export const mul16s = (a, b) => truncInt16(a * b)
export const div16s = (a, b) => truncInt16(div(a, b))
export const shl16s = (a, b) => truncInt16(a << b)
export const shr16s = (a, b) => truncInt16(a >> b)

//Int32
export const truncInt32 = x => x & 0xffffffff

export const truncBigInt32 = x => Number(BigInt.asIntN(32, x))

export const add32s = (a, b) => truncInt32(a + b)
export const sub32s = (a, b) => truncInt32(a - b)
export const div32s = (a, b) => truncInt32(div(a, b))

export const mul32s = (a, b) => {
  const res = a * b;
  if (res <= Number.MIN_SAFE_INTEGER || res >= Number.MAX_SAFE_INTEGER) {
    return truncInt32((a & 0xffff) * b + (b & 0xffff) * (a & 0xffff0000))
  } else {
    return truncInt32(res)
  }
}

//Int64
export const truncBigInt64 = x => BigInt.asIntN(64, x)

export const add64s = (a, b) => truncBigInt64(a + b)
export const sub64s = (a, b) => truncBigInt64(a - b)
export const mul64s = (a, b) => truncBigInt64(a * b)
export const shl64s = (a, b) => truncBigInt64(a << b)
export const div64s = (a, b) => truncBigInt64(divBigInt(a, b))
export const shr64s = (a, b) => truncBigInt64(a >> b)

//Bits8
export const truncUInt8 = x => x & 0xff

export const truncUBigInt8 = x => Number(BigInt.asUintN(8, x))

export const add8u = (a, b) => (a + b) & 0xff
export const sub8u = (a, b) => (a - b) & 0xff
export const mul8u = (a, b) => (a * b) & 0xff
export const div8u = (a, b) => Math.trunc(a / b)
export const shl8u = (a, b) => (a << b) & 0xff
export const shr8u = (a, b) => (a >> b) & 0xff

//Bits16
export const truncUInt16 = x => x & 0xffff

export const truncUBigInt16 = x => Number(BigInt.asUintN(16, x))

export const add16u = (a, b) => (a + b) & 0xffff
export const sub16u = (a, b) => (a - b) & 0xffff
export const mul16u = (a, b) => (a * b) & 0xffff
export const div16u = (a, b) => Math.trunc(a / b)
export const shl16u = (a, b) => (a << b) & 0xffff
export const shr16u = (a, b) => (a >> b) & 0xffff

//Bits32
export const truncUBigInt32 = x => Number(BigInt.asUintN(32, x))

export const truncUInt32 = x => {
  const res = x & -1;
  return res < 0 ? res + 0x100000000 : res;
}

export const add32u = (a, b) => truncUInt32(a + b)
export const sub32u = (a, b) => truncUInt32(a - b)
export const mul32u = (a, b) => truncUInt32(mul32s(a, b))
export const div32u = (a, b) => Math.trunc(a / b)

export const shl32u = (a, b) => truncUInt32(a << b)
export const shr32u = (a, b) => truncUInt32(a <= 0x7fffffff ? a >> b : (b == 0 ? a : (a >> b) ^ ((-0x80000000) >> (b - 1))))
export const and32u = (a, b) => truncUInt32(a & b)
export const or32u = (a, b) => truncUInt32(a | b)
export const xor32u = (a, b) => truncUInt32(a ^ b)

//Bits64
export const truncUBigInt64 = x => BigInt.asUintN(64, x)

export const add64u = (a, b) => BigInt.asUintN(64, a + b)
export const mul64u = (a, b) => BigInt.asUintN(64, a * b)
export const div64u = (a, b) => a / b
export const shl64u = (a, b) => BigInt.asUintN(64, a << b)
export const shr64u = (a, b) => BigInt.asUintN(64, a >> b)
export const sub64u = (a, b) => BigInt.asUintN(64, a - b)

//String
export const strReverse = x => x.split('').reverse().join('')

export const substr = (o, l, x) => x.slice(o, o + l)
