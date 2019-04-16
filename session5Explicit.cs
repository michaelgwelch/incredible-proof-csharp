using System;


struct Session5Explicit
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

    And<A,Imply<B,False>> E9<A,B>(Imply<Imply<A,B>,False> premise)
    {
        // Case 1:
        // Given A
        // Given B
        // Conclude: A ^ (B -> False)
        Imply<(A,B),And<A,Imply<B,False>>> case1 = tuple =>
        {
            A a = tuple.Item1;
            B b = tuple.Item2;

            // Assume A and conclude B to get A -> B
            // Note we use _ instead of a because the name a is already used.
            Imply<A,B> aImpliesB = _ => b;
            
            // We can conclude False by premise
            False fls = premise(aImpliesB);

            // Derivce our conclusion using Absurd
            var localConclusion = Absurd<And<A,Imply<B,False>>>(fls);
            return localConclusion;
        };

        // Case 2:
        // Given A
        // Given B -> False
        // Conclude: A ^ (B -> False)
        Imply<(A,Imply<B,False>),And<A,Imply<B,False>>> case2 = tuple => 
        {
            A a = tuple.Item1;
            Imply<B,False> bImpliesFalse = tuple.Item2;

            // Derive conclusion
            var localConclusion = new And<A,Imply<B,False>>(a,bImpliesFalse);
            return localConclusion;
        };

        // Case 3:
        // Given A -> False
        // B doesn't matter
        // Conclude: A ^ (B -> False)
        Imply<Imply<A,False>,And<A,Imply<B,False>>> case3 = aImpliesFalse =>
        {
            // We can derive A -> B
            Imply<A,B> aImpliesB = a =>
            {
                False fls = aImpliesFalse(a);
                B b = Absurd<B>(fls);
                return b;
            };

            // With premise that gives us False
            False fls_ = premise(aImpliesB);

            // False allows us to derive local conclusion A & (B -> False)
            var localConclusion = Absurd<And<A,Imply<B,False>>>(fls_);
            return localConclusion;
        };


        // Now that we've proven each individual case, put it all together
        // using Excluded Middel
        // Given A v (A -> False)
        // Given B v (B -> False)
        var aOrAImpliesFalse = ExcludedMiddle<A>();
        var bOrBImpliesFalse = ExcludedMiddle<B>();

        var conclusion = aOrAImpliesFalse.CaseAnalysis(
            a => bOrBImpliesFalse.CaseAnalysis(
                // case 1: A & B
                b => case1((a,b)),
                // case 2: A & (B -> False)
                bImpliesFalse => case2((a,bImpliesFalse))
            ),
            // case 3: (A -> False)
            aImpliesFalse => case3(aImpliesFalse)
        );

        return conclusion;
    }
}