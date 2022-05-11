#! /usr/bin/sh

FILES="examples/Benchmarks/*"
OUTPUT=$1
echo "Outputting results to $OUTPUT"

echo "TestName, StaticMem, DynamicMem, FreedMem, MaxMemHeld, Instructions, Reads, Writes" > $OUTPUT

for benchmark in $FILES
do
    echo "Running benchmark $benchmark..."
    TEST=$(basename -s ".stfl" "$benchmark")
    RESULT=$(stack run "$benchmark" -- --output-csv)
    echo "$TEST, $RESULT" >> $OUTPUT
done

