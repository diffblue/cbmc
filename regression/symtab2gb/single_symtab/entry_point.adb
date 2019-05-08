procedure Entry_Point is
  X : constant Integer := 11;
begin
  -- Failure
  pragma Assert (X < 10);
  -- Success
  pragma Assert (X > 0);
end Entry_Point;
