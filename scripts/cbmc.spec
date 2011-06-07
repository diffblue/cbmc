Name:   cbmc
Version:	3.9
Release:	1%{?dist}
Summary:	bounded model checker for C and C++ programs



Group:	Applications
License:	BSD 4-clause
URL:		http://www.cprover.org
Source0:  http://www.minisat.se/downloads/minisat-2.2.0.tar.gz
Source1:	cbmc-3.9.tar.gz
BuildRoot:	%(mktemp -ud %{_tmppath}/%{name}-%{version}-%{release}-XXXXXX)

Requires:	gcc

%description
CBMC generates traces that demonstrate how an assertion can be violated, or
proves that the assertion cannot be violated within a given number of loop
iterations.

%prep
%setup -q -c cbmc+minisat
%setup -q -c cbmc+minisat -T -D -a 1

%build
mv minisat minisat-2.2.0
cd minisat-2.2.0
make MROOT=$PWD -C simp
cd ..
make -C cbmc-3.9/trunk/src/big-int
make -C cbmc-3.9/trunk/src/util
make -C cbmc-3.9/trunk/src %{?_smp_mflags}


%install
rm -rf $RPM_BUILD_ROOT
mkdir -p %{buildroot}/%{_bindir}
for b in goto-cc goto-instrument cbmc ; do cp cbmc-3.9/trunk/src/$b/$b %{buildroot}/%{_bindir} ; done
strip %{buildroot}/%{_bindir}/*


%clean
rm -rf $RPM_BUILD_ROOT


%files
%defattr(-,root,root,-)
%doc
%{_bindir}/goto-cc
%{_bindir}/goto-instrument
%{_bindir}/cbmc


%changelog

