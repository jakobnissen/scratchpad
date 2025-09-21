using BenchmarkTools

function btime(f, strings)
    n = 0
    for i in strings
        n += f(Int, i)
    end
    return n
end

run_parse = false

# Parse small positive ints
ints = [string(rand(0:50)) for i in 1:1000];
run_parse || @btime btime(parse, $ints) seconds = 3
run_parse && @btime btime(parse2, $ints) seconds = 3

# Parse small ints (pos or neg)
ints = [string(rand(-50:50)) for i in 1:1000];
run_parse || @btime btime(parse, $ints) seconds = 3
run_parse && @btime btime(parse2, $ints) seconds = 3

# Larger positive ints
ints = [string(rand(0:10_000_000)) for i in 1:1000];
run_parse || @btime btime(parse, $ints) seconds = 3
run_parse && @btime btime(parse2, $ints) seconds = 3

# Smaller ints with space
ints = [(' '^rand(1:10)) * string(rand(0:100)) * "  " for i in 1:1000];
run_parse || @btime btime(parse, $ints) seconds = 3
run_parse && @btime btime(parse2, $ints) seconds = 3

# Typemax and typemin
ints = [string(rand(Bool) ? typemax(Int) : typemin(Int)) for i in 1:1000];
run_parse || @btime btime(parse, $ints) seconds = 3
run_parse && @btime btime(parse2, $ints) seconds = 3

# Small, hex
ints = map(1:1000) do i
    i = rand(0:50)
    "0x" * string(i; base = 16)
end;
run_parse || @btime btime(parse, $ints) seconds = 3
run_parse && @btime btime(parse2, $ints) seconds = 3

# Small, also negative, hex
ints = map(1:1000) do i
    i = rand(0:200)
    prefix = rand(Bool) ? "" : "-"
    prefix * "0x" * string(i; base = 16)
end;
run_parse || @btime btime(parse, $ints) seconds = 3
run_parse && @btime btime(parse2, $ints) seconds = 3

# Large, hex
ints = map(1:1000) do i
    i = rand(0:10000000)
    "0x" * string(i; base = 16)
end;
run_parse || @btime btime(parse, $ints) seconds = 3
run_parse && @btime btime(parse2, $ints) seconds = 3

function btime_bool(f, strings)
    n = 0
    for i in strings
        n += f(Bool, i)
    end
    return n
end

# Bool numbers
bools = [string(rand(0:1)) for i in 1:1000];
run_parse || @btime btime_bool(parse, $bools) seconds = 3
run_parse && @btime btime_bool(parse2, $bools) seconds = 3

# Bool numbers with leading zeros
bools = ["00" * string(rand(0:1)) for i in 1:1000];
run_parse || @btime btime_bool(parse, $bools) seconds = 3
run_parse && @btime btime_bool(parse2, $bools) seconds = 3

# Bool text
bools = [rand(Bool) ? "true" : "false" for i in 1:1000];
run_parse || @btime btime_bool(parse, $bools) seconds = 3
run_parse && @btime btime_bool(parse2, $bools) seconds = 3
