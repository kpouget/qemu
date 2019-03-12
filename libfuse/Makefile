VER = 2.9.7
SRC = https://github.com/libfuse/libfuse/releases/download/fuse-${VER}/fuse-${VER}.tar.gz

CONFIG_OPT = --enable-lib --enable-static --enable-util --disable-example

ARCH ?= $(shell arch)

ifeq (${ARCH},arm64)
	CONFIG_CROSS_COMPILE = --host=aarch64-linux-gnu
else
ifeq (${ARCH},aarch64)
	CONFIG_CROSS_COMPILE = --host=aarch64-linux-gnu
else
ifneq (${ARCH},x86_64)
$(error Unknown architecture (${ARCH}))
endif
endif
endif

SRC_PATH ?= $(PWD)/libfuse
DESTDIR ?= $(PWD)/libfuse

PREPARED = $(SRC_PATH)/src/fuse-${VER}/configure
CONFIGURED =  $(DESTDIR)/build/${ARCH}/Makefile
BUILT = $(DESTDIR)/build/${ARCH}/lib/.libs/libfuse.so.${VER}
INSTALLED = $(DESTDIR)/install/${ARCH}/lib/libfuse.so.${VER}

all: install

prepare: ${PREPARED}
configure: ${CONFIGURED}
build: ${BUILT}
install: ${INSTALLED}

${PREPARED}:
	@echo '# Preparing libfuse for ${ARCH} $(SRC_PATH)  $(PWD)'

	@mkdir -p $(SRC_PATH)/src $(DESTDIR)/tmp

	@[ ! -f $(SRC_PATH)/src/$(shell basename ${SRC}) ] && cd $(SRC_PATH)/src && \
		echo "Downloading source file from ${SRC}" && \
		curl -O -J -L  ${SRC} || true

	@[ ! -d $(SRC_PATH)/src/fuse-${VER} ] && cd $(SRC_PATH)/src && \
		echo "Extracting $(shell basename ${SRC})" && \
	    tar xf $(shell basename ${SRC}) && \
		cd .. && patch -p1 < $(SRC_PATH)/fix_include_errors.patch || true

${CONFIGURED}: ${PREPARED}
	@echo '# Configuring libfuse for ${ARCH}'
	@mkdir -p $(DESTDIR)/build/${ARCH}
	@cd $(DESTDIR)/build/${ARCH} && \
	$(SRC_PATH)/src/fuse-${VER}/configure ${CONFIG_CROSS_COMPILE} ${CONFIG_OPT} --prefix=/ TMPDIR=$(DESTDIR)/ CFLAGS="-Wno-unused-result" --enable-static

${BUILT}: ${CONFIGURED}
	@echo '# Building libfuse for ${ARCH}'
	@cd $(DESTDIR)/build/${ARCH} && \
	make

${INSTALLED}: ${BUILT}
	@echo '# Installing libfuse for ${ARCH}'
	@mkdir -p $(DESTDIR)/install/${ARCH}
	@cd $(DESTDIR)/build/${ARCH} && \
	make DESTDIR=$(DESTDIR)/install/${ARCH} install && \
	chmod 4755 $(DESTDIR)/install/${ARCH}/bin/fusermount && \
	echo "Success!" || echo "Failure :("

clean:
	@echo '# Cleaning up libfuse ${ARCH}'
	rm -rf $(DESTDIR)/build/${ARCH} $(DESTDIR)/install/${ARCH} $(DESTDIR)/tmp

mrclean: clean
	rm -rf $(DESTDIR)/{build,install}

distclean: mrclean
	rm -rf $(SRC_PATH)/src

#.PHONY: _first clean install build configure prepare all
