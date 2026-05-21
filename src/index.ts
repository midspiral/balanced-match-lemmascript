export const balanced = (
  a: string | RegExp,
  b: string | RegExp,
  str: string,
) => {
  const ma = a instanceof RegExp ? maybeMatch(a, str) : a
  const mb = b instanceof RegExp ? maybeMatch(b, str) : b

  const r = ma !== null && mb != null && range(ma, mb, str)

  return (
    r && {
      start: r[0],
      end: r[1],
      pre: str.slice(0, r[0]),
      body: str.slice(r[0] + ma.length, r[1]),
      post: str.slice(r[1] + mb.length),
    }
  )
}

const maybeMatch = (reg: RegExp, str: string) => {
  const m = str.match(reg)
  return m ? m[0] : null
}

export const range = (
  a: string,
  b: string,
  str: string,
): undefined | [number, number] => {
  //@ verify
  //@ requires a.length > 0
  //@ requires b.length > 0
  //@ ensures \result !== undefined ==> \result.length === 2
  //@ ensures \result !== undefined ==> \result[0] >= 0 && \result[0] + a.length <= str.length
  //@ ensures \result !== undefined ==> \result[1] >= 0 && \result[1] + b.length <= str.length
  //@ ensures \result !== undefined ==> str.slice(\result[0], \result[0] + a.length) === a
  //@ ensures \result !== undefined ==> str.slice(\result[1], \result[1] + b.length) === b
  let begs: number[],
    beg: number | undefined,
    left: number,
    right: number | undefined = undefined,
    result: undefined | [number, number]
  let ai = str.indexOf(a)
  let bi = str.indexOf(b, ai + 1)
  let i = ai

  if (ai >= 0 && bi > 0) {
    if (a === b) {
      return [ai, bi]
    }
    begs = []
    left = str.length

    while (i >= 0 && !result) {
      //@ invariant ai === -1 || (ai >= 0 && ai + a.length <= str.length && str.slice(ai, ai + a.length) === a)
      //@ invariant bi === -1 || (bi >= 0 && bi + b.length <= str.length && str.slice(bi, bi + b.length) === b)
      //@ invariant ai === -1 || ai >= i
      //@ invariant bi === -1 || bi >= i
      //@ decreases (result === undefined ? 1 : 0) + (ai >= 0 ? str.length - ai : 0) + (bi >= 0 ? str.length - bi : 0)
      if (i === ai) {
        begs.push(i)
        ai = str.indexOf(a, i + 1)
      } else if (begs.length === 1) {
        const r = begs.pop()
        if (r !== undefined) result = [r, bi]
      } else {
        beg = begs.pop()
        if (beg !== undefined && beg < left) {
          left = beg
          right = bi
        }

        bi = str.indexOf(b, i + 1)
      }

      i = ai < bi && ai >= 0 ? ai : bi
    }

    if (begs.length && right !== undefined) {
      result = [left, right]
    }
  }

  return result
}
