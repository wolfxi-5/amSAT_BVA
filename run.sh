#!/bin/sh

# 检查参数数量
if [ $# -ne 2 ]; then
    echo "使用方法: $0 <基准测试实例路径> <输出文件夹路径>"
    exit 1
fi

# 获取参数
benchmark_path="$1"
output_dir="$2"

# 检查输入文件是否存在
if [ ! -f "$benchmark_path" ]; then
    echo "错误：基准测试实例文件不存在: $benchmark_path"
    exit 1
fi

# 创建输出目录（如果不存在）
mkdir -p "$output_dir"

# 设置输出文件路径
proof_file="$output_dir/proof.out"

# TODO: 在这里添加处理基准测试实例的命令
./sources/simp/glucose -drup -verb=0 $benchmark_path -drup-file=$proof_file

# echo "处理完成"
# echo "证明已保存到: $proof_file"