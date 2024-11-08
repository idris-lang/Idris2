export function js2idris_array(x) {
  let acc = { h: 0 };

  for (let i = x.length - 1; i >= 0; i--) {
    acc = { a1: x[i], a2: acc };
  }
  return acc;
}

export function idris2js_array(x) {
  const result = Array();
  while (x.h === undefined) {
    result.push(x.a1); x = x.a2;
  }
  return result;
}


export const fastUnpack = (str) => js2idris_array(Array.from(str))
export const fastConcat = (xs) => idris2js_array(xs).join('')
export const fastPack = (xs) => idris2js_array(xs).join('')
