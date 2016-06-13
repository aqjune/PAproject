/* quiz */

a := 1; 
b := 2; 

x := readInt; 
if (x) (p := &a) (p := 10); 
if (x) (p := &b) (p := p + 1); 
/* p must be (odd, {b}) here, not (odd, {a, b}). Why? */ 
if (x) (c := *p) (c := 4)

/* c is even */
