function btime(f, strings)
    n = 0
    for i in strings
        n += f(Int, i)
    end
    return n
end

run_parse = true

# Parse small positive ints
ints = [string(rand(0:50)) for i in 1:1000];
run_parse || @btime btime(parse, $ints) seconds = 3
run_parse && @btime btime(parse2, $ints) seconds = 3

# Parse small ints
ints = [string(rand(-50:50)) for i in 1:1000];
run_parse || @btime btime(parse, $ints) seconds = 3
run_parse && @btime btime(parse2, $ints) seconds = 3

# Larger positive ints
ints = [string(rand(0:10_000_000)) for i in 1:1000];
run_parse || @btime btime(parse, $ints) seconds = 3
run_parse && @btime btime(parse2, $ints) seconds = 3

# Smaller ints with space
ints = [(' '^rand(1:10)) * string(rand(0:10_000_000)) * "  " for i in 1:1000];
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
