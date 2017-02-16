Name:		zlog
Version:	1
Release:	1%{?dist}
Summary:	distributed shared log
License:	LGPL-2.1
Source0:	zlog-1.tar.gz

BuildRequires:	cmake
BuildRequires:	gcc-c++
BuildRequires:	boost-devel
BuildRequires:	protobuf-devel
BuildRequires:	protobuf-compiler
BuildRequires:	java-devel
BuildRequires:	lcov

%description
distributed shared log

%prep
%setup -q

%build
make %{?_smp_mflags}

%install

%files
