../../LLVM/install/bin/opt -S -load ../../Pass/build/libReachingDefinition.so -ReachingDefinition < $1 > /dev/null 2> $1.out
