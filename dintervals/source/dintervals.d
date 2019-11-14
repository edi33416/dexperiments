import std.experimental.checkedint;
import std.stdio;

struct IntervalAbort(T)
{
    this(T min, T max)
    {
        minVal = min;
        maxVal = max;
    }

    T min(T)()
    {
        return minVal;
    }

    T max(T)()
    {
        return maxVal;
    }

static:
    /**

    Called automatically upon a bad cast (one that loses precision or attempts
    to convert a negative value to an unsigned type). The source type is `Src`
    and the destination type is `Dst`.

    Params:
    src = The source of the cast

    Returns: Nominally the result is the desired value of the cast operation,
    which will be forwarded as the result of the cast. For `Abort`, the
    function never returns because it aborts the program.

    */
    Dst onBadCast(Dst, Src)(Src src)
    {
        Warn.onBadCast!Dst(src);
        assert(0);
    }

    /**

    Called automatically upon a bounds error.

    Params:
    rhs = The right-hand side value in the assignment, after the operator has
    been evaluated
    bound = The value of the bound being violated

    Returns: Nominally the result is the desired value of the operator, which
    will be forwarded as result. For `Abort`, the function never returns because
    it aborts the program.

    */
    T onLowerBound(Rhs, T)(Rhs rhs, T bound)
    {
        Warn.onLowerBound(rhs, bound);
        assert(0);
    }
    /// ditto
    T onUpperBound(Rhs, T)(Rhs rhs, T bound)
    {
        Warn.onUpperBound(rhs, bound);
        assert(0);
    }

    /**

    Called automatically upon a comparison for equality. In case of a erroneous
    comparison (one that would make a signed negative value appear equal to an
    unsigned positive value), this hook issues `assert(0)` which terminates the
    application.

    Params:
    lhs = The first argument of `Checked`, e.g. `int` if the left-hand side of
      the operator is `Checked!int`
    rhs = The right-hand side type involved in the operator

    Returns: Upon a correct comparison, returns the result of the comparison.
    Otherwise, the function terminates the application so it never returns.

    */
    static bool hookOpEquals(Lhs, Rhs)(Lhs lhs, Rhs rhs)
    {
        bool error;
        auto result = opChecked!"=="(lhs, rhs, error);
        if (error)
        {
            Warn.hookOpEquals(lhs, rhs);
            assert(0);
        }
        return result;
    }

    /**

    Called automatically upon a comparison for ordering using one of the
    operators `<`, `<=`, `>`, or `>=`. In case the comparison is erroneous (i.e.
    it would make a signed negative value appear greater than or equal to an
    unsigned positive value), then application is terminated with `assert(0)`.
    Otherwise, the three-state result is returned (positive if $(D lhs > rhs),
    negative if $(D lhs < rhs), `0` otherwise).

    Params:
    lhs = The first argument of `Checked`, e.g. `int` if the left-hand side of
      the operator is `Checked!int`
    rhs = The right-hand side type involved in the operator

    Returns: For correct comparisons, returns a positive integer if $(D lhs >
    rhs), a negative integer if  $(D lhs < rhs), `0` if the two are equal. Upon
    a mistaken comparison such as $(D int(-1) < uint(0)), the function never
    returns because it aborts the program.

    */
    int hookOpCmp(Lhs, Rhs)(Lhs lhs, Rhs rhs)
    {
        bool error;
        auto result = opChecked!"cmp"(lhs, rhs, error);
        if (error)
        {
            Warn.hookOpCmp(lhs, rhs);
            assert(0);
        }
        return result;
    }

    /**

    Called automatically upon an overflow during a unary or binary operation.

    Params:
    x = The operator, e.g. `-`
    lhs = The left-hand side (or sole) argument
    rhs = The right-hand side type involved in the operator

    Returns: Nominally the result is the desired value of the operator, which
    will be forwarded as result. For `Abort`, the function never returns because
    it aborts the program.

    */
    typeof(~Lhs()) onOverflow(string x, Lhs)(Lhs lhs)
    {
        Warn.onOverflow!x(lhs);
        assert(0);
    }
    /// ditto
    typeof(Lhs() + Rhs()) onOverflow(string x, Lhs, Rhs)(Lhs lhs, Rhs rhs)
    {
        Warn.onOverflow!x(lhs, rhs);
        assert(0);
    }

private:

    T minVal = T.min;
    T maxVal = T.max;
}

struct Interval(alias LowerB, alias UpperB)
if ((is(LowerB == Checked!(T, H), T, H) || is(typeof(LowerB) == Checked!(T, H), T, H))
     && (is(UpperB == Checked!(T2, H2), T2, H2) || is(typeof(UpperB) == Checked!(T2, H2), T2, H2)))
{
    import std.traits;

    //alias LB = is(typeof(LowerB)) ? typeof(LowerB) : LowerB;
    static if (is(typeof(LowerB)))
    {
        alias LB = typeof(LowerB);
    }
    else
    {
        alias LB = LowerB;
    }
    static if (is(typeof(UpperB)))
    {
        alias UB = typeof(UpperB);
    }
    else
    {
        alias UB = UpperB;
    }

    LB start;
    UB end;

    invariant()
    {
        assert(start <= end, "Invalid interval boundaries");
    }

    this(LB lb, UB ub)
    {
        start = lb;
        end = ub;
    }

    this(Interval i)
    {
        start = i.start;
        end = i.end;
    }

    enum hasCTFEBounds = is (typeof({ enum x = LowerB; enum y = UpperB; }));

    //enum isUnitInterval = hasCTFEBounds && LowerB >= 0 && UpperB <= 1;
    static if (hasCTFEBounds)
    {
        enum isUnitInterval = LowerB >= 0 && UpperB <= 1;
    }
    else
    {
        private bool isUnitInterval()
        {
            return start >= 0 && end <= 1;
        }
    }

    bool opEquals(Rhs)(const auto ref Rhs rhs)
    //if (is (Rhs == Interval!(L, U), L, U) && is (L : LB) && is (U : UB))
    //TODO: why is the constraint failing
    {
        return start == rhs.start && end == rhs.end;
    }

    auto opBinary(string op, Rhs)(const auto ref Rhs rhs)
    if (isIntegral!Rhs || isFlotingPoint!Rhs)
    {
        alias R = typeof(mixin("start" ~ op ~ "rhs"));
        static if (hasCTFEBounds && isUnitInterval && op == "*")
        {
            mixin("auto s = LB(start.get" ~ op ~ "rhs);");
            mixin("auto e = LB(end.get" ~ op ~ "rhs);");
            auto r = Interval(s, e);
            return r;
        }
        else
        {
            auto tmp = this;
            mixin("tmp.start = start" ~ op ~ "rhs;");
            mixin("tmp.end = end" ~ op ~ "rhs;");
            return tmp;
        }
    }

    auto opOpAssign(string op, Rhs)(const auto ref Rhs rhs)
    if (isIntegral!Rhs || isFlotingPoint!Rhs)
    {
        alias R = typeof(mixin("start" ~ op ~ "rhs"));
        static if (hasCTFEBounds && isUnitInterval && op == "*")
        {
            mixin("start = start.get" ~ op ~ "rhs;");
            mixin("end = end.get" ~ op ~ "rhs;");
            return this;
        }
        else
        {
            mixin("start = start" ~ op ~ "rhs;");
            mixin("end = end" ~ op ~ "rhs;");
            return this;
        }
    }
}

//struct Interval(size_t LowerB, size_t UpperB)
//{
//}

@system unittest
{
    //auto i = Interval!(Checked!(int, IntervalAbort!int)(0, IntervalAbort!int(0, 1)),
                       //Checked!(int, IntervalAbort!int)(1, IntervalAbort!int(0, 1)))();
    auto i = Interval!(0.checked, 1.checked)();
    auto i2 = Interval!(Checked!int, Checked!int)(0.checked, 2.checked);
    auto x = i + 2;
    auto x2 = i2 + 2;
    assert(i != x2);
    assert(i == i);
    //writeln(x);
}
