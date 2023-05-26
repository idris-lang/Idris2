#!/usr/bin/env node --stack-size=80984

function testStackSize(depth) {
    console.log(depth)
    if (depth) testStackSize(depth - 1)
}

console.log("start")
testStackSize(984)
console.log("done")

testStackSize(80984)


