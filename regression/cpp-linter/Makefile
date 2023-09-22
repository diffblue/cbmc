default: tests.log

test:
	@../test.pl -p -c 'C:/ProgramData/chocolatey/bin/python3.12.exe ../../../scripts/cpplint.py --repository=../../../'

tests.log: ../test.pl
	@../test.pl -p -c 'C:/ProgramData/chocolatey/bin/python3.12.exe ../../../scripts/cpplint.py --repository=../../../'

clean:
	find . -name '*.out' -execdir $(RM) '{}' \;
	find . -name '*.gb' -execdir $(RM) '{}' \;
	$(RM) tests.log
