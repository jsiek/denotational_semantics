%.agdai: %.agda
	agda  $<

#	BelowBCDConst.agda \
#	FunInverseBCDConst.agda \
#	CurryBCDConst.agda \

AGDA =  Utilities.agda \
	Primitives.agda \
	\
	MultiStep.agda \
	Lambda.agda \
	EvalCallByName.agda \
	LambdaCallByValue.agda \
	EvalCallByValue.agda \
	ISWIM.agda \
	EvalISWIM.agda \
	\
	Structures.agda \
	ValueStructAux.agda \
	OrderingAux.agda \
	Consistency.agda \
	ConsistentAux.agda \
	ValueConst.agda \
	ValueBCD.agda \
	CurryConst.agda \
	PrimConst.agda \
	ModelCurryConst.agda \
	WFDenotMod.agda \
	CurryApplyStruct.agda \
	CurryApplyAux.agda \
	ModelCallByName.agda \
	ModelCallByValue.agda \
	ModelISWIM.agda \
	\
	LambdaDenot.agda \
	ISWIMDenot.agda \
	ISWIMDenotAlt.agda \
	Compositionality.agda \
	RenamePreserveReflect.agda \
	Filter.agda \
	SubstitutionPreserve.agda \
	SubstitutionReflect.agda \
	SoundnessCallByName.agda \
	SoundnessCallByValue.agda \
	SoundnessISWIM.agda \
	AdequacyCallByName.agda \
	AdequacyCallByValue.agda \
	AdequacyISWIM.agda 

AGDAI = $(AGDA:%.agda=%.agdai)

all: ${AGDA} ${AGDAI}

clean:
	rm -f *.agdai *~
