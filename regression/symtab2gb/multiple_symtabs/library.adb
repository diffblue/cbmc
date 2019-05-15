procedure Library (X : Integer) is
begin
  -- Failure
  pragma Assert (X < 10);
  -- Success
  pragma Assert (X > 0);
end Library;
