using System;


struct Session5
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
        // Only in logic blocks (axioms) can we cheat and use unsafe features
        // These aren't meant to be called. Proof only involve the type checker.
        return default(T);
    }


    static Or<A, Imply<A, False>> ExcludedMiddle<A>()
    {
        // Only in logic blocks (axioms) can we cheat and use unsafe features
        // These aren't meant to be called. Proof only involve the type checker.
        return Or.Left<A, Imply<A, False>>(default(A));
    }



    Or<A, Imply<A, False>> E1<A>()
    {
        return ExcludedMiddle<A>();
    }

    Imply<A, B> E2<A, B>(Imply<Imply<B, False>, Imply<A, False>> premise)
    {
        return a => ExcludedMiddle<B>().CaseAnalysis(
                b => b,
                bImpliesFalse => Absurd<B>(premise(bImpliesFalse)(a))
            );
    }

    Or<Imply<A,False>,Imply<B,False>> E3<A,B>(Imply<And<A,B>,False> premise)
    {
        return ExcludedMiddle<A>().CaseAnalysis(
            a => ExcludedMiddle<B>().CaseAnalysis(
                b => Absurd<Or<Imply<A,False>,Imply<B,False>>>(premise(new And<A,B>(a,b))),
                bImpliesFalse => Or.Right<Imply<A,False>,Imply<B,False>>(bImpliesFalse)
            ), //
            aImpliesFalse => Or.Left<Imply<A,False>,Imply<B,False>>(aImpliesFalse)
        );
    }

    A E4<A>(Imply<Imply<A,False>,False> premise)
    {
        return ExcludedMiddle<A>().CaseAnalysis(
            a => a,
            aImpliesFalse => Absurd<A>(premise(aImpliesFalse))
        );
    }

    Or<Imply<A,False>,B> E5<A,B>(Imply<A,B> premise)
    {
        return ExcludedMiddle<A>().CaseAnalysis(
            a => Or.Right<Imply<A,False>,B>(premise(a)) ,
            aImpliesFalse => Or.Left<Imply<A,False>,B>(aImpliesFalse)
        );
    }

    Or<Imply<A,False>,C> E6<A,B,C>(Imply<A,B> prem1, Imply<B,C> prem2)
    {
        return ExcludedMiddle<A>().CaseAnalysis(
            a => Or.Right<Imply<A,False>,C>(prem2(prem1(a))),
            aImpliesFalse => Or.Left<Imply<A,False>,C>(aImpliesFalse)
        );
    }

    Imply<Imply<Imply<A,B>,A>,A> E7<A,B>()
    {
        return premise => ExcludedMiddle<A>().CaseAnalysis(
                a => a,
                aImpliesFalse => premise(a => Absurd<B>(aImpliesFalse(a)))
            );
    }

    // E8


    And<A,Imply<B,False>> E9<A,B>(Imply<Imply<A,B>,False> premise)
    {
        return ExcludedMiddle<A>().CaseAnalysis(
            a => ExcludedMiddle<B>().CaseAnalysis(
                b => Absurd<And<A,Imply<B,False>>>(premise(_ => b)),
                bImpliesFalse => new And<A,Imply<B,False>>(a, bImpliesFalse)
            ),
            aImpliesFalse => Absurd<And<A,Imply<B,False>>>(premise(a => Absurd<B>(aImpliesFalse(a))))
        );

    }

}