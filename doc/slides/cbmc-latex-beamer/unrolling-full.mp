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

  for s=0 step 1 until 4:
    z[s] = (1.2cm,s*ystep);
  endfor;

  dotlabel.ulft ("L1", z[4]);
  dotlabel.lft  ("L2", z[3]);
  dotlabel.lft  ("L3", z[2]);
  dotlabel.llft ("L4", z[1]);
  dotlabel.lft  ("L5", z[0]);

  for s=0 step 1 until 3:
    connect (z[s+1],z[s]);
  endfor;
  
  drawarrow (z[4] shifted (0,0.3cm))..z[4] cutafter fullcircle scaled 3pt shifted z[4];
  drawarrow z[3]..(2.2cm,ypart z[3])..z[3] cutbefore fullcircle scaled 3pt shifted z[3] cutafter fullcircle scaled 3pt shifted z[3];

endfig;

beginfig (1)
  % FSOFT unrolling
  defaultscale:=9pt/fontsize defaultfont;
  
  for s=0 step 1 until 6:
    for t=1 step 1 until 5:
      z[5*s+t]=(t*1cm,s*ystep);
      draw z[5*s+t] withcolor 0.5white withpen pencircle scaled 3pt;
%      if ((t=3) and ((s=4) or (s=2) or (s=0))):
%	label.urt ("L"&decimal t, z[5*s+t]) withcolor 0.5white;
%      elseif ((s=6) and (t=2)):
%	label.lft ("L"&decimal t, z[5*s+t]) withcolor 0.5white;
%      else:
	label.llft ("L"&decimal t, z[5*s+t]) withcolor 0.5white;
%      fi;
    endfor;

    label.lft ("#"&decimal (6-s), (0, s*ystep));

    if (not (s=6)):
      draw (0,(ystep/2)+(s)*ystep)..(5.5cm,(ystep/2)+(s)*ystep) dashed evenly;
    fi;
  endfor

%  drawarrow (z[5*6+1] shifted (0,0.3cm))..z[5*6+1] cutafter fullcircle scaled 3pt shifted z[5*6+1];
  
  connect (z[5*6+1], z[5*5+2]); label.llft ("L1", z[5*6+1]); label.llft ("L2", z[5*5+2]);
  connect (z[5*5+2], z[5*4+3]); label.llft ("L3", z[5*4+3]);
  connect (z[5*4+3], z[5*3+4]); label.llft ("L4", z[5*3+4]);
  connect (z[5*3+4], z[5*2+5]); label.llft ("L5", z[5*2+5]);
  connect (z[5*5+2], z[5*4+2]); label.llft ("L2", z[5*4+2]);
  connect (z[5*4+2], z[5*3+3]); label.llft ("L3", z[5*3+3]);
  connect (z[5*3+3], z[5*2+4]); label.llft ("L4", z[5*2+4]);
  connect (z[5*2+4], z[5*1+5]); label.llft ("L5", z[5*1+5]);
  connect (z[5*4+2], z[5*3+2]); label.llft ("L2", z[5*3+2]);
  connect (z[5*3+2], z[5*2+3]); label.llft ("L3", z[5*2+3]);
  connect (z[5*2+3], z[5*1+4]); label.llft ("L4", z[5*1+4]);
  connect (z[5*1+4], z[5*0+5]); label.llft ("L5", z[5*0+5]);
  connect (z[5*3+2], z[5*2+2]); label.llft ("L2", z[5*2+2]);
  connect (z[5*2+2], z[5*1+3]); label.llft ("L3", z[5*1+3]);
  connect (z[5*1+3], z[5*0+4]); label.llft ("L4", z[5*0+4]);
  connect (z[5*2+2], z[5*1+2]); label.llft ("L2", z[5*1+2]);
  connect (z[5*1+2], z[5*0+3]); label.llft ("L3", z[5*0+3]);
  connect (z[5*1+2], z[5*0+2]); label.llft ("L2", z[5*0+2]);

%  draw z[5*0+3]..(z[5*0+3] shifted (-0.5cm,-(ystep/3))) dashed withdots scaled 0.5;
%  draw z[5*0+3]..(z[5*0+3] shifted (0.5cm,-(ystep/3))) dashed withdots scaled 0.5;
  
endfig;

