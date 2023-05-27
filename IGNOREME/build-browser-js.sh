# optionally a browser build
# - require("fs") -> require("browserify-fs") in the node js
npx browserify ./build-node-js/idris2.node.js --detect-globals --full-paths --standalone idris2 -o ./build-node-js/idris2.browser.js
# needed fixes:
# - process.stdout.write(x) -> console.log(x)
# - process.argv = ["idris2", "--no-prelude"];
# - process.chdir noop
# - process.stdout.columns -> 80