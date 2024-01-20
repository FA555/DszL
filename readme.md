# DszL

这是一份北京邮电大学计算机科学与技术专业 2021 级大三上（2023–2024
学年度秋季学期）《程序设计实践》课程大作业。

这定语叠得够吧。

## 别废话，哥们怎么运行

```shell
cargo run --release -- --help # 接下来的参数自己看吧，懒得写了
# ↓不介意的话可以试试这个，你可以跟它说句⎡我要退学⎦。
cargo run --release -- -f examples/test5.dszl -r gui

cargo doc --no-deps --open # API 文档

cargo test --release # 跑一下测试
```

什么？你没 Rust / Cargo？

```shell
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh # 原神，启动！
```

## 然后呢？

剩下的就不是这里该说的了。更多信息参见[给课程交上去的报告](./doc/main.pdf)
。报告当时是一天水出来的，内容比较幽默，别介意。
