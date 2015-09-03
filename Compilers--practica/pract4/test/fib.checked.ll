; ModuleID = 'test/fib.checked.bc'

@format = private unnamed_addr constant [4 x i8] c"%d\0A\00"
@format1 = private unnamed_addr constant [3 x i8] c"%d\00"
@__assertion = private unnamed_addr constant [30 x i8] c"Array out of bounds detected.\00"
@__file = private unnamed_addr constant [6 x i8] c"fib.c\00"

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
  %fib = alloca [100000 x i32]
  %n = alloca i32
  store i32 100000, i32* %n
  %0 = getelementptr [100000 x i32]* %fib, i32 0, i32 0, !dbg !4
  store i32 1, i32* %0, !dbg !4
  %1 = getelementptr [100000 x i32]* %fib, i32 0, i32 1, !dbg !5
  store i32 1, i32* %1, !dbg !5
  br label %for.init, !dbg !5

for.init:                                         ; preds = %entry
  %j = alloca i32, !dbg !5
  store i32 0, i32* %j, !dbg !5
  br label %for.cond, !dbg !5

for.cond:                                         ; preds = %for.inc, %for.init
  %2 = load i32* %j, !dbg !6
  %3 = icmp slt i32 %2, 100000, !dbg !6
  br i1 %3, label %for.body, label %for.end, !dbg !6

for.body:                                         ; preds = %for.cond
  br label %for.init1, !dbg !6

for.inc:                                          ; preds = %for.end5
  %4 = load i32* %j, !dbg !7
  %5 = add i32 %4, 1, !dbg !7
  store i32 %5, i32* %j, !dbg !8
  br label %for.cond, !dbg !8

for.end:                                          ; preds = %for.cond
  ret i32 0, !dbg !8

for.init1:                                        ; preds = %for.body
  %i = alloca i32, !dbg !6
  store i32 2, i32* %i, !dbg !6
  br label %for.cond2, !dbg !6

for.cond2:                                        ; preds = %for.inc4, %for.init1
  %6 = load i32* %i, !dbg !9
  %7 = load i32* %n, !dbg !10
  %8 = icmp slt i32 %6, %7, !dbg !9
  br i1 %8, label %for.body3, label %for.end5, !dbg !9

for.body3:                                        ; preds = %for.cond2
  %9 = load i32* %i, !dbg !11
  %isoutofbounds = icmp sle i32 100000, %9, !dbg !11
  %isnegative = icmp slt i32 %9, 0, !dbg !11
  %throwassert = or i1 %isoutofbounds, %isnegative, !dbg !11
  br i1 %throwassert, label %10, label %11, !dbg !11, !prof !12

; <label>:10                                      ; preds = %for.body3
  call void (i8*, i8*, i32, ...)* @__assert(i8* getelementptr inbounds ([30 x i8]* @__assertion, i32 0, i32 0), i8* getelementptr inbounds ([6 x i8]* @__file, i32 0, i32 0), i32 9), !dbg !11
  unreachable, !dbg !11

; <label>:11                                      ; preds = %for.body3
  %12 = getelementptr [100000 x i32]* %fib, i32 0, i32 %9, !dbg !11
  %13 = load i32* %i, !dbg !13
  %14 = sub i32 %13, 2, !dbg !13
  %15 = getelementptr [100000 x i32]* %fib, i32 0, i32 %14, !dbg !13
  %16 = load i32* %15, !dbg !14
  %17 = load i32* %i, !dbg !15
  %18 = sub i32 %17, 1, !dbg !15
  %19 = getelementptr [100000 x i32]* %fib, i32 0, i32 %18, !dbg !15
  %20 = load i32* %19, !dbg !16
  %21 = add i32 %16, %20, !dbg !14
  store i32 %21, i32* %12, !dbg !17
  br label %for.inc4, !dbg !17

for.inc4:                                         ; preds = %11
  %22 = load i32* %i, !dbg !18
  %23 = add i32 %22, 1, !dbg !18
  store i32 %23, i32* %i, !dbg !19
  br label %for.cond2, !dbg !19

for.end5:                                         ; preds = %for.cond2
  br label %for.inc, !dbg !19
}

; Function Attrs: noreturn
declare void @__assert(i8*, i8*, i32, ...) #1

attributes #0 = { nounwind }
attributes #1 = { noreturn }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!3}

!0 = metadata !{i32 786449, metadata !1, i32 2, metadata !"Cheetah Compiler", i1 false, metadata !"", i32 0, metadata !2, metadata !2, metadata !2, metadata !2, metadata !2, metadata !"", i32 1} ; [ DW_TAG_compile_unit ] [test/fib.c] [DW_LANG_C]
!1 = metadata !{metadata !"fib.c", metadata !"test"}
!2 = metadata !{}
!3 = metadata !{i32 2, metadata !"Debug Info Version", i32 1}
!4 = metadata !{i32 4, i32 1, metadata !0, null}
!5 = metadata !{i32 5, i32 1, metadata !0, null}
!6 = metadata !{i32 7, i32 16, metadata !0, null}
!7 = metadata !{i32 7, i32 32, metadata !0, null}
!8 = metadata !{i32 7, i32 28, metadata !0, null}
!9 = metadata !{i32 8, i32 18, metadata !0, null} ; [ DW_TAG_imported_declaration ]
!10 = metadata !{i32 8, i32 22, metadata !0, null} ; [ DW_TAG_imported_declaration ]
!11 = metadata !{i32 9, i32 9, metadata !0, null}
!12 = metadata !{metadata !"branch_weights", i32 1, i32 10000000}
!13 = metadata !{i32 9, i32 18, metadata !0, null}
!14 = metadata !{i32 9, i32 14, metadata !0, null}
!15 = metadata !{i32 9, i32 29, metadata !0, null}
!16 = metadata !{i32 9, i32 25, metadata !0, null}
!17 = metadata !{i32 9, i32 5, metadata !0, null}
!18 = metadata !{i32 8, i32 29, metadata !0, null} ; [ DW_TAG_imported_declaration ]
!19 = metadata !{i32 8, i32 25, metadata !0, null} ; [ DW_TAG_imported_declaration ]
