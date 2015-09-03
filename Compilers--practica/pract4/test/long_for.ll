; ModuleID = 'long_for'

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
  %n = alloca i32
  store i32 9999, i32* %n
  %sum = alloca i32
  store i32 0, i32* %sum
  %foo = alloca [10000 x i32]
  br label %for.init

for.init:                                         ; preds = %entry
  %j = alloca i32
  store i32 0, i32* %j
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %for.init
  %0 = load i32* %j, !dbg !4
  %1 = icmp slt i32 %0, 100000, !dbg !4
  br i1 %1, label %for.body, label %for.end, !dbg !4

for.body:                                         ; preds = %for.cond
  br label %for.init1, !dbg !4

for.inc:                                          ; preds = %for.end5
  %2 = load i32* %j, !dbg !5
  %3 = add i32 %2, 1, !dbg !5
  store i32 %3, i32* %j, !dbg !6
  br label %for.cond, !dbg !6

for.end:                                          ; preds = %for.cond
  ret i32 0, !dbg !6

for.init1:                                        ; preds = %for.body
  %i = alloca i32, !dbg !4
  store i32 0, i32* %i, !dbg !4
  br label %for.cond2, !dbg !4

for.cond2:                                        ; preds = %for.inc4, %for.init1
  %4 = load i32* %i, !dbg !7
  %5 = load i32* %n, !dbg !8
  %6 = icmp slt i32 %4, %5, !dbg !7
  br i1 %6, label %for.body3, label %for.end5, !dbg !7

for.body3:                                        ; preds = %for.cond2
  %7 = load i32* %sum, !dbg !9
  %8 = load i32* %i, !dbg !10
  %9 = add i32 %7, %8, !dbg !9
  store i32 %9, i32* %sum, !dbg !11
  %10 = load i32* %n, !dbg !12
  %11 = getelementptr [10000 x i32]* %foo, i32 0, i32 %10, !dbg !12
  %12 = load i32* %sum, !dbg !13
  store i32 %12, i32* %11, !dbg !14
  br label %for.inc4, !dbg !14

for.inc4:                                         ; preds = %for.body3
  %13 = load i32* %i, !dbg !15
  %14 = add i32 %13, 1, !dbg !15
  store i32 %14, i32* %i, !dbg !16
  br label %for.cond2, !dbg !16

for.end5:                                         ; preds = %for.cond2
  br label %for.inc, !dbg !16
}

attributes #0 = { nounwind }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!3}

!0 = metadata !{i32 786449, metadata !1, i32 2, metadata !"Cheetah Compiler", i1 false, metadata !"", i32 0, metadata !2, metadata !2, metadata !2, metadata !2, metadata !2, metadata !"", i32 1} ; [ DW_TAG_compile_unit ] [test/long_for.c] [DW_LANG_C]
!1 = metadata !{metadata !"long_for.c", metadata !"test"}
!2 = metadata !{}
!3 = metadata !{i32 2, metadata !"Debug Info Version", i32 1}
!4 = metadata !{i32 5, i32 17, metadata !0, null}
!5 = metadata !{i32 5, i32 33, metadata !0, null}
!6 = metadata !{i32 5, i32 29, metadata !0, null}
!7 = metadata !{i32 6, i32 19, metadata !0, null}
!8 = metadata !{i32 6, i32 23, metadata !0, null}
!9 = metadata !{i32 7, i32 11, metadata !0, null}
!10 = metadata !{i32 7, i32 17, metadata !0, null}
!11 = metadata !{i32 7, i32 5, metadata !0, null}
!12 = metadata !{i32 8, i32 9, metadata !0, null} ; [ DW_TAG_imported_declaration ]
!13 = metadata !{i32 8, i32 14, metadata !0, null} ; [ DW_TAG_imported_declaration ]
!14 = metadata !{i32 8, i32 5, metadata !0, null} ; [ DW_TAG_imported_declaration ]
!15 = metadata !{i32 6, i32 30, metadata !0, null}
!16 = metadata !{i32 6, i32 26, metadata !0, null}
