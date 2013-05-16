verbatimtex
%&latex
\documentclass[10pt]{article}
\usepackage{color}
\begin{document}
etex

input boxes

vardef connect(suffix s, t)=
  drawarrow s..t cutbefore fullcircle scaled 3pt shifted s cutafter fullcircle scaled 3pt shifted t;
  drawdot s withpen pencircle scaled 3pt;
  drawdot t withpen pencircle scaled 3pt;
enddef;

vardef connectred(suffix s, t)=
  drawdot s withpen pencircle scaled 5pt withcolor red;
  drawdot t withpen pencircle scaled 5pt withcolor red;
  pickup pencircle scaled 1.1;
  drawarrow s..t cutbefore fullcircle scaled 5pt shifted s
    cutafter fullcircle scaled 5pt shifted t withcolor red;
  pickup pencircle scaled .5;
enddef;

vardef doall=
  defaultscale:=9pt/fontsize defaultfont;

  z[0] = (-.2cm,7*ystep); % if
  z[1] = ( 0cm,6*ystep); % switch
  z[2] = (.2cm,5*ystep); % case 0
  z[3] = (.4cm,4*ystep); % case 1
  z[4] = (.6cm,3*ystep); % case 2
  z[5] = (.8cm,2*ystep); % case 3
  z[6] = (1cm,1*ystep); % default
  z[7] = (0cm,0*ystep); % end

  z[12] = z[2]-(.5cm,.5cm); % case 0
  z[13] = z[3]-(.5cm,.5cm); % case 1
  z[14] = z[4]-(.5cm,.5cm); % case 2
  z[15] = z[5]-(.5cm,.5cm); % case 3

  dotlabel.rt  ("if", z[0]);
  dotlabel.rt  ("switch", z[1]);
  dotlabel.rt  ("case 0", z[2]);
  dotlabel.rt  ("case 1", z[3]);
  dotlabel.rt  ("case 2", z[4]);
  dotlabel.rt  ("case 3", z[5]);
  dotlabel.rt  ("default", z[6]);
  dotlabel.rt  ("", z[7]);

  dotlabel.rt  ("", z[12]);
  dotlabel.rt  ("", z[13]);
  dotlabel.rt  ("", z[14]);
  dotlabel.rt  ("", z[15]);

  connect(z[0], z[1]);
  connect(z[1], z[2]);
  connect(z[2], z[3]);
  connect(z[3], z[4]);
  connect(z[4], z[5]);
  connect(z[5], z[6]);

  connect(z[2], z[12]);
  connect(z[3], z[13]);
  connect(z[4], z[14]);
  connect(z[5], z[15]);

  connect(z[12], z[7]);
  connect(z[13], z[7]);
  connect(z[14], z[7]);
  connect(z[15], z[7]);

  connect(z[6], z[7]);

  label.rt  (btex \color{blue}\small$0\le t \le 79$ etex, z[0]+(.2cm,-ystep/2));
  label.rt  (btex \color{blue}\small$t/20\not=0$ etex, z[2]+(.2cm,-ystep/2));
  label.rt  (btex \color{blue}\small$t/20\not=1$ etex, z[3]+(.2cm,-ystep/2));
  label.rt  (btex \color{blue}\small$t/20\not=2$ etex, z[4]+(.2cm,-ystep/2));
  label.rt  (btex \color{blue}\small$t/20\not=3$ etex, z[5]+(.2cm,-ystep/2));

  % for the bounding box
  label ("", z[7]-(0cm,.1cm));
  
enddef;

ystep = 1.0cm;

beginfig (0)
  % Control flow graph of SHA example
  doall;
endfig;

beginfig (1)
  % Control flow graph of SHA example

  doall;

  connectred(z[0], z[1]);
  connectred(z[1], z[2]);
  connectred(z[2], z[3]);
  connectred(z[3], z[13]);
  connectred(z[13],z[7]);
  
endfig;

beginfig (2)
  % Control flow graph of SHA example

  doall;

  connectred(z[0], z[1]);
  connectred(z[1], z[2]);
  connectred(z[2], z[3]);
  connectred(z[3], z[4]);
  connectred(z[4], z[5]);
  connectred(z[5], z[6]);
  
endfig;

verbatimtex
\end{document}
etex
