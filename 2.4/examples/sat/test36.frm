begin
p1 v (n3:n2 ^ n3:(n2 ^ n1));
n2 v <R1>(n3:n1 ^ n3:!p1);
p1 v n2:!n1;
!p1 v <R1>(!n1 ^ n1:n2 ^ n1:!n3)
end
