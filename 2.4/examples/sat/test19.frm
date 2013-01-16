begin
(p1 -> (false -> <R1>[R2](p3)));
[R2]<R1>(p1 <--> [R2](p1 v p2 v p3));
[R1][R1][R2](p1 -> [R1](p2 <--> <R2>p1));
(!p1 v !p3) -> (n1:n2);
<R1>!p1 v !p3;
<R1><R2>(!p1 v !p3) <--> <R3>(!p1 v !p3);
[R2][R1](n1:!p1 v !p3)
end                                                                                             
