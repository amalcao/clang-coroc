set(LLVM_LINK_COMPONENTS
  Support
  )

add_clang_library(clangAnalysis
  AnalysisDeclContext.cpp
  BodyFarm.cpp
  CFG.cpp
  CFGReachabilityAnalysis.cpp
  CFGStmtMap.cpp
  CallGraph.cpp
  CocoaConventions.cpp
  Consumed.cpp
  CodeInjector.cpp
  Dominators.cpp
  DataflowWorklist.cpp
  FormatString.cpp
  LiveVariables.cpp
  ObjCNoReturn.cpp
  PostOrderCFGView.cpp
  PrintfFormatString.cpp
  ProgramPoint.cpp
  PseudoConstantAnalysis.cpp
  ReachableCode.cpp
  ScanfFormatString.cpp
  ThreadSafety.cpp
  ThreadSafetyCommon.cpp
  ThreadSafetyLogical.cpp
  ThreadSafetyTIL.cpp
  UninitializedValues.cpp

  LINK_LIBS
  clangAST
  clangBasic
  clangLex
  )
