with One;
procedure Two is
   X : Integer := 1;
begin
   One (X);
   pragma Assert (X=2);
end Two;
