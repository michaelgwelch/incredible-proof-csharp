using System;

struct Session2
{



    struct And<X,Y>
    {
        public readonly X x;
        public readonly Y y;

        public And(X x, Y y)
        {
            this.x = x;
            this.y = y;
        }
    }

    public delegate TResult Imply<in T,out TResult>(T arg);

    

    public Imply<A,C> E5<A,B,C>(Imply<A,B> prem1, Imply<B,C> prem2)
    {
        return a => prem2(prem1(a));
    }
}