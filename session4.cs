using System;

struct Session4
{
    struct And<Left, Right>
    {
        public readonly Left item1;
        public readonly Right item2;

        public And(Left x, Right y)
        {
            this.item1 = x;
            this.item2 = y;
        }
    }

    public delegate TResult Imply<in T, out TResult>(T arg);

    public static class Or
    {

        public static Or<L, R> Left<L, R>(L l)
        {
            return new LeftImpl<L, R>(l);
        }

        public static Or<L, R> Right<L, R>(R r)
        {
            return new RightImpl<L, R>(r);
        }

        private class LeftImpl<Left, Right> : Or<Left, Right>
        {
            private readonly Left l;
            public LeftImpl(Left l)
            {
                this.l = l;
            }
            public T CaseAnalysis<T>(Imply<Left, T> leftProof, Imply<Right, T> rightProof)
            {
                return leftProof(l);
            }
        }

        private class RightImpl<Left, Right> : Or<Left, Right>
        {
            private readonly Right r;
            public RightImpl(Right r)
            {
                this.r = r;
            }
            public T CaseAnalysis<T>(Imply<Left, T> leftProof, Imply<Right, T> rightProof)
            {
                return rightProof(r);
            }
        }
    }

    public interface Or<L, R>
    {
        T CaseAnalysis<T>(Imply<L, T> leftProof, Imply<R, T> rightProof);
    }

    class False
    {
        private False() { }
    }

    static T Absurd<T>(False n)
    {
        // Absurd is one of our axioms. We obviously aren't proving it
        throw new Exception("axiom - no proof needed");
    }

    A E1<A>(False premise) => Absurd<A>(premise);

    A E2Part1<A>(False premise) => Absurd<A>(premise);
    B E2Part2<B>(False premise) => Absurd<B>(premise);

    Or<False, A> E3<A>(A premise) => Or.Right<False, A>(premise);

    A E4<A>(Or<False, A> premise)
    {
        return premise.CaseAnalysis(
            fls => Absurd<A>(fls),
            a => a
        );
    }

    False E5<A>(And<False, A> premise) => premise.item1;

    Imply<False, A> E6<A>() => fls => Absurd<A>(fls);

    Imply<Imply<B, False>, Imply<A, False>> E7<A, B>(Imply<A, B> premise)
    {
        return bImpliesFalse => a => bImpliesFalse(premise(a));
    }

    And<Imply<A, False>, Imply<B, False>> E8<A, B>(Imply<Or<A, B>, False> premise)
    {
        return new And<Imply<A, False>, Imply<B, False>>(
            a => premise(Or.Left<A, B>(a)),
            b => premise(Or.Right<A, B>(b))
        );
    }

    Imply<Or<A, B>, False> E9<A, B>(And<Imply<A, False>, Imply<B, False>> premise)
    {
        return aorb => aorb.CaseAnalysis(
            a => premise.item1(a),
            b => premise.item2(b)
        );
    }

    Imply<And<A, B>, False> E10<A, B>(Or<Imply<A, False>, Imply<B, False>> premise)
    {
        return aandb => premise.CaseAnalysis(
            aImpliesFalse => aImpliesFalse(aandb.item1),
            bImpliesFalse => bImpliesFalse(aandb.item2)
        );
    }

    Imply<A, False> E11<A>(Imply<Imply<Imply<A, False>, False>, False> premise)
    {
        return a => premise(aImpliesFalse => aImpliesFalse(a));
    }

    Imply<A, B> E12<A, B>(Or<Imply<A, False>, B> premise)
    {
        return a => premise.CaseAnalysis(
            aImpliesFalse => Absurd<B>(aImpliesFalse(a)),
            b => b
        );
    }

    Imply<B, False> E13<A, B>(Imply<A, False> prem1, Imply<B, A> prem2)
    {
        return b => prem1(prem2(b));
    }


    Imply<And<And<A, B>, C>, False> E14<A, B, C>(Or<Or<Imply<A, False>, Imply<B, False>>, Imply<C, False>> premise)
    {
        return a_b_c => premise.CaseAnalysis(
            afalseOrBfalse => afalseOrBfalse.CaseAnalysis(
                afalse => afalse(a_b_c.item1.item1),
                bfalse => bfalse(a_b_c.item1.item2)
            ),
            cfalse => cfalse(a_b_c.item2)
        );
    }


    Imply<Imply<Or<A, Imply<A, False>>, False>, False> E15<A>()
    {
        return premise =>
             premise(Or.Right<A, Imply<A, False>>(a =>
                  premise(Or.Left<A, Imply<A, False>>(a))));
    }

}