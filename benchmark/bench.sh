#!/bin/bash

# potential TODO: make tests recursive to allow nicer organisation of tests

TESTS_ROOT=benchmarks

# timeout threshold in seconds (this may be nice to have as a named param)
TIMEOUT=15

# defaults for the optionals
FILENAME="bench-results"
BACKEND="chez"
BUILD=false
FAST=false

function usage {
        echo 'Perform all benchmarks in the Idris2 benchmark suite. Command output is written to a csv file.'
        echo
        echo "Usage: $(basename $0) [OPTION]..." 2>&1
        echo '   -b   build each test first'
        echo '   -c   specify the backend to use during compilation (requires -b flag)'
        echo '        must be one of chez, refc, racket, gambit'
        echo '        (default is chez)'
        echo '   -f   perform a faster version of the benchmark'
        echo '   -o   specify name of output csv file'
        echo '        (default is `bench-results_$BACKEND[_fast]`)'
        echo '   -h   shows this message'
        echo
        echo 'e.g. bench -fbc refc -o myrefcoutput'
        exit 1
}

# begin args parsing
optstring=":bc:fo:h"
while getopts ${optstring} arg; do
  case "${arg}" in
    # whether to build
    b) BUILD=true ;;
    # set codegen (redundant unless -b passed)
    c)  case $2 in
            chez|refc|racket|gambit)
              BACKEND="$2"
              export IDRIS2_CG=$BACKEND ;;
            *)  
              echo "$BACKEND is not a recognised backend! You can check the available backends using $0 -h"
              exit 1 ;;
        esac
        ;;
    # test speed flag
    f) FAST=true ;;
    # custom output file name
    o) 
      [[ ! -z "$2" ]] && FILENAME="$2"
		  echo "-o option passed, with value $FILENAME"
		  ;;
    # help message
    h) usage ;;
    \?)
      echo "Invalid option: -${OPTARG}."
      echo
      usage
      ;;
    :) echo "Option -$OPTARG requires an argument" >&2; exit 1 ;;
  esac
done
# end args parsing

#begin tests
cwd=$(pwd)
if [ $FILENAME != "bench-results" ]; 
then 
   echo here
   output_path="$FILENAME.csv"; 
else 
   output_path="$cwd/${FILENAME}_${BACKEND}"
   if [[ $FAST = true ]]; then output_path+="_fast"; fi
   output_path+=".csv"
fi

echo "benchmark,elapsed,user,system" > $output_path
cd $TESTS_ROOT

dashes='-------------------------------'

tests=`ls -d ./*/`
ntests=$(echo $tests | wc -w)
n=1
for test in $tests
do
  # clean test name
  test=${test%/}
  test=${test#./}
  echo $dashes
  echo "[$n/$ntests] current test:" $test
  echo $dashes
  cd $test

  # build test if necessary
  if ! test -f "build/exec/${test}" || [ "$BUILD" = true ]; then
    echo building $test...
    [[ -f $infile.in ]] && rm -r build
    idris2 -o $test $test.idr # - currently do not have a way to handle compilation errors (todo?)
  fi
  # begin test
  echo executing build/exec/$test
  # set in stream to relevant input file if present
  [[ $FAST = true ]] && infile="${test}_fast" || infile="$test"
  [[ -f $infile.in ]] && exec 3<"${infile}.in" || exec 3<&0
  # time it, eat stdout
  timeout -s SIGINT $TIMEOUT /usr/bin/time -f "${test},%e,%U,%S" -o ${output_path} -a build/exec/${test} <&3 > /dev/null 2>&1
  if [ $? -eq 124 ]; then
     echo "benchmark failed! (timeout after ${TIMEOUT}s)"
  fi
  # end test
  cd ..
  ((n+=1))
done

echo $dashes
echo "benchmarks complete! data written to $output_path"
# end tests