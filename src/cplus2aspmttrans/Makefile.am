include $(top_srcdir)/src/Makefile.shared

lib_LIBRARIES = libcplusode.bin.a
bin_PROGRAMS = cplusode.bin

BUILT_SORCES =\
	Configuration.cpp


libcplusode_bin_a_SOURCES = \
	Configuration.cpp \
	Translator.cpp \
	SortData.cpp \
	ObjectData.cpp \
	RangeData.cpp \
	ConstantData.cpp \
	Context.cpp

libcplusode_bin_a_CPPFLAGS = $(BOOST_CPPFLAGS)

cplusode_bin_SOURCES = \
	main.cpp

cplusode_bin_CPPFLAGS = $(BOOST_CPPFLAGS)
cplusode_bin_LDFLAGS = $(BOOST_FILESYSTEM_LDFLAGS) $(BOOST_SYSTEM_LDFLAGS) $(BOOST_THREAD_LDFLAGS)
cplusode_bin_LDADD = libcplusode.bin.a -lbcplusodeparser $(BOOST_FILESYSTEM_LIBS) $(BOOST_SYSTEM_LIBS) $(BOOST_THREAD_LIBS)
