; ModuleID = 'test/dynamic_index.checked.bc'

@format = private unnamed_addr constant [4 x i8] c"%d\0A\00"
@format1 = private unnamed_addr constant [3 x i8] c"%d\00"
@__assertion = private unnamed_addr constant [30 x i8] c"Array out of bounds detected.\00"
@__file = private unnamed_addr constant [16 x i8] c"dynamic_index.c\00"

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
  %n = alloca i32
  store i32 5, i32* %n
  %0 = load i32* %n, !dbg !4
  %isoutofbounds = icmp sle i32 10, %0, !dbg !4
  %isnegative = icmp slt i32 %0, 0, !dbg !4
  %throwassert = or i1 %isoutofbounds, %isnegative, !dbg !4
  br i1 %throwassert, label %1, label %2, !dbg !4, !prof !5

; <label>:1                                       ; preds = %entry
  call void (i8*, i8*, i32, ...)* @__assert(i8* getelementptr inbounds ([30 x i8]* @__assertion, i32 0, i32 0), i8* getelementptr inbounds ([16 x i8]* @__file, i32 0, i32 0), i32 2), !dbg !4
  unreachable, !dbg !4

; <label>:2                                       ; preds = %entry
  %3 = getelementptr [10 x i32]* %foo, i32 0, i32 %0, !dbg !4
  store i32 0, i32* %3, !dbg !6
  ret i32 0, !dbg !6
}

; Function Attrs: noreturn
declare void @__assert(i8*, i8*, i32, ...) #1

attributes #0 = { nounwind }
attributes #1 = { noreturn }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!3}

!0 = metadata !{i32 786449, metadata !1, i32 2, metadata !"Cheetah Compiler", i1 false, metadata !"", i32 0, metadata !2, metadata !2, metadata !2, metadata !2, metadata !2, metadata !"", i32 1} ; [ DW_TAG_compile_unit ] [test/dynamic_index.c] [DW_LANG_C]
!1 = metadata !{metadata !"dynamic_index.c", metadata !"test"}
!2 = metadata !{}
!3 = metadata !{i32 2, metadata !"Debug Info Version", i32 1}
!4 = metadata !{i32 2, i32 5, metadata !0, null}
!5 = metadata !{metadata !"branch_weights", i32 1, i32 10000000}
!6 = metadata !{i32 2, i32 1, metadata !0, null}
