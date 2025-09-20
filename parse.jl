# How to use:
# In the REPL, evaluate in Base (write Base, then press alt+M)
# `include(Base, "parse.jl")`
# To update code, comment out the baremodule ParseNumberErrors, and the import
# below it, then re-include.

import Base.Checked: add_with_overflow, mul_with_overflow

# https://github.com/JuliaLang/julia/pull/59606
@inline function _unsafe_new_substring(s::AbstractString)
    return @inbounds @inline SubString{typeof(s)}(s, 0, ncodeunits(s), Val{:noshift}())
end

_unsafe_new_substring(s::SubString) = s

@inline function _unsafe_new_substring(s::AbstractString, offset::Int, ncodeunits::Int)
    return @inbounds @inline SubString{typeof(s)}(s, offset, ncodeunits, Val{:noshift}())
end

@inline function _unsafe_skip_codeunits(s::SubString, codeunits::Int)
    offset = s.offset
    return _unsafe_new_substring(parent(s), offset + codeunits, ncodeunits(s) - codeunits)
end

function fast_isspace(c::AbstractChar)
    (c == ' ' || '\t' <= c <= '\r' || c == '\u85') && return true
    return slow_isspace(c)
end

@noinline function slow_isspace(c::AbstractChar)
    return '\ua0' <= c && Base.Unicode.category_code(c) == Base.Unicode.UTF8PROC_CATEGORY_ZS
end

# https://github.com/JuliaLang/julia/pull/59615
@propagate_inbounds thisind(s::SubString{String}, i::Int) = _thisind_str(s, i)
@propagate_inbounds nextind(s::SubString{String}, i::Int) = _nextind_str(s, i)

"""
    parse(type, str; base)

Parse a string as a number. For `Integer` types, a base can be specified
(the default is 10). For floating-point types, the string is parsed as a decimal
floating-point number.  `Complex` types are parsed from decimal strings
of the form `"R±Iim"` as a `Complex(R,I)` of the requested type; `"i"` or `"j"` can also be
used instead of `"im"`, and `"R"` or `"Iim"` are also permitted.
If the string does not contain a valid number, an error is raised.

!!! compat "Julia 1.1"
    `parse(Bool, str)` requires at least Julia 1.1.

# Examples
```jldoctest
julia> parse(Int, "1234")
1234

julia> parse(Int, "1234", base = 5)
194

julia> parse(Int, "afc", base = 16)
2812

julia> parse(Float64, "1.2e-3")
0.0012

julia> parse(Complex{Float64}, "3.2e-1 + 4.5im")
0.32 + 4.5im
```
"""
parse(T::Type, str; base = Int)

struct BadBase
    # The `nothing` here signifies the user passed in a type which
    # cannot be represented as an `Int`
    base::Union{Nothing, Int}

    function BadBase(x::Integer)
        base = if in(x, typemin(Int):typemax(Int))
            x % Int
        else
            nothing
        end
        return new(base)
    end
end

struct BadDigit
    base::UInt8
    digit_codeunit::UInt8
end

struct MisMatchingBase
    observed::UInt8
    given::UInt8
end

baremodule ParseNumberErrors
    import ..@enum
    @enum ParseNumberError::UInt8 begin
        whitespace_string
        premature_end
        overflow
        extra_after_whitespace
        bad_imaginary
        # NB: float parsing is done in C, so we don't get to know what went wrong
        bad_float
    end
end

using .ParseNumberErrors: ParseNumberError

struct ParseIntError
    pos::Int
    error::Union{BadBase, BadDigit, MisMatchingBase, ParseNumberError}
end

@noinline function throw_parse_int_error(error::ParseIntError)
    kind = error.error
    return if kind isa BadBase
        base = kind.base
        if base === nothing
            throw(ArgumentError("invalid base: base must be 2 ≤ base ≤ 62"))
        else
            throw(ArgumentError("invalid base: base must be 2 ≤ base ≤ 62, got $base"))
        end
    elseif kind isa BadDigit
        throw(ArgumentError("invalid base $(kind.base) digit $(repr(Char(kind.digit_codeunit))) at index $(error.pos)"))
    elseif kind isa MisMatchingBase
        prefix = if kind.observed == 0x02
            "0b"
        elseif kind.observed == 0x08
            "0o"
        else
            "0x"
        end
        throw(ArgumentError("Error when parsing integer: Observed base $(kind.given) does not match integer prefix \"$(prefix)\""))
    else
        if kind == ParseNumberErrors.whitespace_string
            throw(ArgumentError("input string is empty or only contains whitespace"))
        elseif kind == ParseNumberErrors.premature_end
            throw(ArgumentError("premature end of integer"))
        elseif kind == ParseNumberErrors.overflow
            # Note: We don't want to print the whole string here, because an overflow often
            # happens when a huge string is being passed in.
            throw(OverflowError("Overflow when parsing integer"))
        elseif kind == ParseNumberErrors.extra_after_whitespace
            throw(ArgumentError("extra characters after whitespace when parsing string"))
        else
            throw(ArgumentError("expected imaginary unit \"im\""))
        end
    end
end

parse(::Type{Union{}}, slurp...; kwargs...) = error("cannot parse a value as Union{}")

function parse(::Type{T}, c::AbstractChar; base::Integer = 10) where {T <: Integer}
    result = parse_internal(T, c, base)
    return result isa Integer ? result : throw_parse_int_error(result)
end

# TODO: Remember to add to PR comment that this method is new
function tryparse(::Type{T}, c::AbstractChar; base::Integer = 10) where {T <: Integer}
    result = parse_internal(T, c, base)
    return result isa Integer ? result : nothing
end

function check_valid_base(base::Integer)::Union{UInt8, ParseIntError}
    2 <= base <= 62 || return ParseIntError(0, BadBase(base))
    return base % UInt8
end

# We use this function to avoid calling lstrip unless necessary, to make the
# code it generates small and likely to inline
function unlikely_lstrip(s::SubString)
    isempty(s) && return s
    # Safety: We just checked s is not empty, so index 1 is always valid
    cu = @inbounds codeunit(s, 1)
    return if (cu in UInt8('\t'):UInt8(' ')) | (cu > 0x7f)
        lstrip(isspace, s)
    else
        s
    end
end

function parse_internal(::Type{T}, c::AbstractChar, base::Integer) where {T <: Integer}
    a::UInt8 = (base <= 36 ? 10 : 36)
    base = check_valid_base(base)
    base isa ParseIntError && return base
    c = Char(c)::Char
    # Note: All `Char` constructors prevent creating multi-char `Char`s.
    # Hence, if the first codeunit is ASCII, that's the only codeunit in the char.
    codeunit = first_utf8_byte(c)
    d = if UInt8('0') ≤ codeunit ≤ UInt8('9')
        codeunit - UInt8('0')
    elseif UInt8('A') ≤ codeunit ≤ UInt8('Z')
        codeunit - UInt8('A') + 0x0a # + 10 for the 10 digits
    elseif UInt8('a') ≤ codeunit ≤ UInt8('z')
        codeunit - UInt8('a') + a
    else
        return ParseIntError(1, BadDigit(base, codeunit))
    end
    d < base || return ParseIntError(1, BadDigit(base, codeunit))
    return convert(T, d)::T
end

function tryparse(::Type{Float64}, s::SubString{String})
    hasvalue, val = @ccall jl_try_substrtod(
        s::Ptr{UInt8},
        0::Csize_t,
        (sizeof(s) % UInt)::Csize_t
    )::Tuple{Bool, Float64}
    return hasvalue ? val : nothing
end

function tryparse(::Type{Float64}, s::SubString{String})
    hasvalue, val = @ccall jl_try_substrtof(
        s::Ptr{UInt8},
        0::Csize_t,
        (sizeof(s) % UInt)::Csize_t
    )::Tuple{Bool, Float32}
    return hasvalue ? val : nothing
end

# Forward parsing to `SubString`, in order to only have one single implementation.
function tryparse(T::Union{Type{Float32}, Type{Float64}}, s::String)
    return tryparse(T, SubString(s))
end

function tryparse(::Type{T}, s::AbstractString) where {T <: Union{Float32, Float64}}
    # Since float parsing is implemented in C, it's not generic over the string type,
    # so we (wastefully) need to copy the string.
    return tryparse(T, String(s)::String)
end

function tryparse(::Type{Float16}, s::AbstractString)
    return convert(Union{Float16, Nothing}, tryparse(Float32, s))
end

# TODO: Named parse2 for now, rename to parse
function parse2(::Type{T}, s::AbstractString; base::Union{Nothing, Integer} = nothing) where {T <: Integer}
    result = @inline parse_internal(T, _unsafe_new_substring(s), base)
    return result isa Integer ? result : throw_parse_int_error(result)
end

function parse_internal(::Type{T}, s::SubString, base::Union{Nothing, Integer}) where {T <: Integer}
    # A base of `nothing` means to determine it from the integer prefix, e.g.
    # 0x -> 16, 0o -> 8.
    if base !== nothing
        base = check_valid_base(base)
        base isa ParseIntError && return base
    end
    ncu = ncodeunits(s)
    # Remove leading whitespace
    s = unlikely_lstrip(s)
    isempty(s) && return ParseIntError(ncu, ParseNumberErrors.whitespace_string)
    # Remove a leading + or - with following optional whitespace, and get the sign
    (is_positive, s) = parseint_sign(s)
    # If starts with 0b, base is 2, 0x -> 16, 0o -> 8, else 10
    (observed_base, s) = parseint_base(s)
    if isnothing(base)
        base = observed_base
    elseif (observed_base != 0x0a) & (base != observed_base)
        # If obsereved base is 10, we did not observe a prefix, so don't throw
        consumed_cu = ncu - ncodeunits(s)
        return ParseIntError(consumed_cu + 2, MisMatchingBase(observed_base, base))
    end
    # A string like "-" or "- 0x" ends prematurely
    isempty(s) && return ParseIntError(ncu, ParseNumberErrors.premature_end)
    # Base 10 is going to be, by far, the most normal case, so optimise for that.
    consumed_cu = ncu - ncodeunits(s)
    return if base == 0x0a
        # Base 10 is by far the most common base, so we inline the happy path of base 10
        # parsing here.
        n = zero(T)
        base = T(10)
        # Most integers are far below typemax/typemin, so as long as we're below max_no_overflow,
        # the next digit can't cause overflow
        max_no_overflow = div(typemax(T) - T(9), base)
        index = 1
        while index ≤ ncodeunits(s)
            n > max_no_overflow && break
            # Safety:
            cu = @inbounds codeunit(s, index)
            digit = cu - UInt8('0')
            digit > 0x09 && break
            n = base * n + T(digit)
            index += 1
        end
        if index > ncodeunits(s)
            return is_positive ? n : -n
        else
            # All the slow conditions (overflow, strange base, spaces in the string etc. go here)
            return parseint_unhappy(n, 0x0a, _unsafe_skip_codeunits(s, index - 1), consumed_cu + index - 1, is_positive)
        end
    elseif base == 0x10
        # Base 16 is the second most popular base. It gets a fast path too, though not inlined into
        # this function.
        parseint_base16(T, s, consumed_cu, is_positive)
    else
        # All other bases go to the slow fallback function.
        parseint_unhappy(T(0), base, s, consumed_cu, is_positive)
    end
end

# Note: This function is efficient (generated little code), but does not inline by itself
@inline function parseint_sign(s::SubString)::Tuple{Bool, SubString{String}}
    # Note: Space must have been stripped off left before, and must not be empty
    cu = @inbounds codeunit(s, 1)
    (sign, has_sign) = if cu == UInt8('+')
        (true, true)
    elseif cu == UInt8('-')
        (false, true)
    else
        (true, false)
    end
    s = if has_sign
        # Safety: This function is only called after an `isempty` check,
        # so we know there is at least 1 codeunit.parseint_sig
        s = unlikely_lstrip(_unsafe_skip_codeunits(s, 1))
    else
        s
    end
    return (sign, s)
end

# Note: This function is efficient (generated little code), but does not inline by itself
@inline function parseint_base(s::SubString)::Tuple{UInt8, SubString{String}}
    # Note: Space must have been stripped off before
    ncodeunits(s) < 2 && return (0x0a, s)
    # Safety: We just checked there are 2 codeunits or more
    (c1, c2) = (@inbounds(codeunit(s, 1)), @inbounds(codeunit(s, 2)))
    # Safety: We checked at least two codeunits just above
    rest = _unsafe_skip_codeunits(s, 2)
    return if (c1, c2) == (UInt8('0'), UInt8('b'))
        (0x02, rest)
    elseif (c1, c2) == (UInt8('0'), UInt8('o'))
        (0x08, rest)
    elseif (c1, c2) == (UInt8('0'), UInt8('x'))
        (0x10, rest)
    else
        (0x0a, s)
    end
end

# A base-16 version of the base 10 version inlines in parse_internal
@noinline function parseint_base16(::Type{T}, s::SubString, consumed_cu::Int, is_positive::Bool) where {T <: Integer}
    n = zero(T)
    base = T(16)
    max_no_overflow = div(typemax(T) - T(15), base)
    index = 1
    while index ≤ ncodeunits(s)
        n > max_no_overflow && break
        cu = @inbounds codeunit(s, index)
        digit = cu - UInt8('0')
        digit > 0x0f && break
        n = base * n + T(digit)
        index += 1
    end
    if index > ncodeunits(s)
        return is_positive ? n : -n
    else
        return parseint_unhappy(n, 0x10, _unsafe_skip_codeunits(s, index - 1), consumed_cu + index - 1, is_positive)
    end
end

@noinline function parseint_unhappy(n::Integer, base::UInt8, s::SubString, consumed_cu::Int, is_positive::Bool)
    T = typeof(n)
    index = 1
    ncu = ncodeunits(s)
    while index ≤ ncu
        cu = @inbounds codeunit(s, index)
        digit = __convert_digit(cu, base)
        if digit >= base
            # We can guarantee this index is valid because all the previous indices
            # were ASCII digits. Also, due to the while loop structure, we can
            # guarantee this is inbounds.
            # Spaces can be non-ASCII so we need to do this part of the loop on chars.
            # We check chars until the end. If all we see is space, we accept and return n.
            # If we see a space, then something else, we return an error alerting the user
            # they can't have space in the middle of a number.
            # If we don't see a space, then we've seen a non-digit and we return that error.
            char = @inbounds s[index]
            seen_space = false
            while fast_isspace(char)
                seen_space = true
                # Safety: We obtained index from a nextind call (or, the first time,
                # see the above comment on safety, and exit on OOB, so this is inbounds)
                index = @inbounds nextind(s, index)
                index > ncu && @goto return_n
                # Safety: We just checked this in inbounds and obtained the index from a nextind call
                char = @inbounds s[index]
            end
            if seen_space
                return ParseIntError(index + consumed_cu, ParseNumberErrors.extra_after_whitespace)
            else
                return ParseIntError(index + consumed_cu, BadDigit(base, first_utf8_byte(char)))
            end
        end
        (new_n, mul_overflowed) = mul_with_overflow(n, T(base))
        (new_n, add_overflowed) = add_with_overflow(new_n, digit % T)
        if (mul_overflowed | add_overflowed)
            # If we're parsing typemin(T), we hit overflow here, but it's not an error.
            # new_n == typemin(T), and then at the end we do -n at the end, which does nothing.
            is_positive | (new_n != typemin(T)) && return ParseIntError(index + consumed_cu, ParseNumberErrors.overflow)
        end
        index += 1
        n = new_n
    end
    @label return_n
    n = is_positive ? n : -n
    return n
end

# '0':'9' -> 0:9
# 'A':'Z' -> 10:35
# 'a':'z' -> 10:35 if base <= 36, 36:61 otherwise
# input outside of that is mapped to base
@inline function __convert_digit(codeunit::UInt8, base::UInt8)
    return if codeunit in UInt8('0'):UInt8('9')
        codeunit - UInt8('0')
    elseif codeunit in UInt8('A'):UInt8('Z')
        codeunit - UInt8('A') + 0x0a
    elseif codeunit in UInt8('a'):UInt8('z')
        a = base <= 36 ? UInt8(10) : UInt8(36)
        codeunit - UInt8('a') + a
    else
        base
    end
end

# Again, this compiles to very little code, so we inline it.
function try_literal(s::Union{String, SubString{String}})
    ncu = ncodeunits(s)
    ncu < 4 && return nothing
    n = (@inbounds(codeunit(s, 1)) % UInt32) |
        ((@inbounds(codeunit(s, 2)) % UInt32) << 8) |
        ((@inbounds(codeunit(s, 3)) % UInt32) << 16) |
        ((@inbounds(codeunit(s, 4)) % UInt32) << 24)
    (ncu == 4) & (n == 0x0000065_75_72_74) && return true
    if ncu == 5
        five = @inbounds codeunit(s, 5)
        (ncu == 4) & (n == 0x0000073_6c_61_66) & (five == 0x65) && return false
    end
    return nothing
end

function parse_internal(::Type{Bool}, s::SubString, base::Union{Integer, Nothing})
    # This is identical to the general case, except for two reasons:
    # We do not accept a leading + or -
    # We also accept "true" and "false"
    if base !== nothing
        base = check_valid_base(base)
        base isa ParseIntError && return base
    end
    ncu = ncodeunits(s)
    s = unlikely_lstrip(s)
    isempty(s) && return ParseIntError(ncu, ParseNumberErrors.whitespace_string)

    # As a special case, we accept literal "true" and "false"
    if s isa Union{String, SubString{String}}
        literal = @inline try_literal(s)
        literal isa Bool && return literal
    else
        s == "true" && return true
        s == "false" && return false
    end

    (observed_base, s) = parseint_base(s)
    if isnothing(base)
        base = observed_base
    elseif (observed_base != 0x0a) & (base != observed_base)
        consumed_cu = ncu - ncodeunits(s)
        return ParseIntError(consumed_cu + 2, MisMatchingBase(observed_base, base))
    end
    return isempty(s) && return ParseIntError(ncu, ParseNumberErrors.premature_end)

    # We don't care about base when parsing bool, because no matter the base,
    # we only accept 0 or 1

    # TODO: Skip any number of zeros, and then one 1.


end

# TODO
# Parse Complex
