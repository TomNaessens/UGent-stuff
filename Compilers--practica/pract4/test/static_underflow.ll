; ModuleID = 'static_underflow'

@format = private unnamed_addr constant [4 x i8] c"%d\0A\00"
@format1 = private unnamed_addr constant [3 x i8] c"%d\00"

declare i32 @printf(i8*, ...)

define internal void @echo(i32) {
entry:
  %1 = call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([4 x i8]* @format, i32 0, i32 0), i32 %0)
  ret void
}

declare i32 @scanf(i8*, ...)

define internal i32 @read() {
entry:
  %toScan = alloca i32
  %0 = call i32 (i8*, ...)* @scanf(i8* getelementptr inbounds ([3 x i8]* @format1, i32 0, i32 0), i32* %toScan)
  %1 = load i32* %toScan
  ret i32 %1
}

; Function Attrs: nounwind
define i32 @main() #0 {
entry:
  %foo = alloca [10 x i32]
  %0 = getelementptr [10 x i32]* %foo, i32 0, i32 -1, !dbg !4
  store i32 0, i32* %0, !dbg !5
  ret i32 0, !dbg !5
}

attributes #0 = { nounwind }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!3}

!0 = metadata !{i32 786449, metadata !1, i32 2, metadata !"Cheetah Compiler", i1 false, metadata !"", i32 0, metadata !2, metadata !2, metadata !2, metadata !2, metadata !2, metadata !"", i32 1} ; [ DW_TAG_compile_unit ] [test/static_underflow.c] [DW_LANG_C]
!1 = metadata !{metadata !"static_underflow.c", metadata !"test"}
!2 = metadata !{}
!3 = metadata !{i32 2, metadata !"Debug Info Version", i32 1}
!4 = metadata !{i32 2, i32 5, metadata !0, null}
!5 = metadata !{i32 2, i32 1, metadata !0, null}