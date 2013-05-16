input boxes

vardef connect(suffix s, t)=
  drawarrow s..t cutbefore fullcircle scaled 3pt shifted s cutafter fullcircle scaled 3pt shifted t;
  drawdot s withpen pencircle scaled 3pt;
  drawdot t withpen pencircle scaled 3pt;
enddef;

ystep = 0.9cm;

beginfig (0)
  % Control flow graph
  defaultscale:=9pt/fontsize defaultfont;

  z[1] = (1.2cm,3*ystep);
  z[2] = (0.4cm,2*ystep);
  z[3] = (2.0cm,2*ystep);
  z[4] = (1.2cm,1*ystep);

  label.top ("L1", z[1]+(0,.1cm));
  dotlabel.top ("", z[1]);
  dotlabel.lft ("L2", z[2]);
  dotlabel.rt  ("L3", z[3]);
  dotlabel.bot ("L4", z[4]);

  connect(z[1], z[2]);
  connect(z[1], z[3]);
  connect(z[2], z[4]);
  connect(z[3], z[4]);
  
  drawarrow z[4]..(3cm,ypart 0.5[z[4],z[1]])..z[1] cutbefore fullcircle scaled 3pt shifted z[4] cutafter fullcircle scaled 3pt shifted z[1];
  
endfig;
