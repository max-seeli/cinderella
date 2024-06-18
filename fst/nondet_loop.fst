model nondet_loop {

var x,i,non_det_1;

states l1,l2,l3;

transition t0_0 := {
 from := l1;
 to := l2;
 guard := i <= x;
 action := x'=x,i'=i;
};

transition t0_1 := {
 from := l1;
 to := l3;
 guard := i > x;
 action := x'=x,i'=i;
};

transition t1_0 := {
 from := l2;
 to := l1;
 guard := non_det_1 >= 0.5 && non_det_1 <= 1.5;
 action := x'=x,i'=non_det_1 + i;
};

}strategy s1 {

Region init := {state=l1 && x > 0 && i = 1};

}