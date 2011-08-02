IDLFILES = MymmsAddin.idl
IDL_DIR = /usr/lib/openoffice/sdk/idl
OUT_COMP_GEN = .
RDBFILE = types.rdb

RM = rm -f

GENURDFILES = $(patsubst %.idl,$(OUT_COMP_GEN)/%.urd,$(IDLFILES))

all : urd rdb clean

urd : $(IDLFILES)
	idlc -I. -I$(IDL_DIR) $^

rdb: $(GENURDFILES)
	regmerge $(RDBFILE) /UCR $^

clean :
	$(RM) $(GENURDFILES)

distclean :
	$(RM) $(GENURDFILES) $(RDBFILE)
