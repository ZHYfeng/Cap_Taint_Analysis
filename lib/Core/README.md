#监听器
目前两个监听器，PSOListener，SymbolicListener。
- listenerKind 标志监听器的类型，方便添加和删除操作。
- 指令执行前、后。大循环前、后。
- 执行失败、创建线程。

1. PSOListener
  - beforeRunMethodAsMain 得到全局变量初值。
  - executeInstruction 得到
  - instructionExecuted
  - afterRunMethodAsMain 统计一些信息

2. SymbolicListener
  - beforeRunMethodAsMain 得到assert的信息。
  - executeInstruction 得到PathCondition.
  - instructionExecuted 在Load执行后创建符号值。
  - afterRunMethodAsMain 统计一些信息

#监听器服务
- start、end 执行逻辑控制
