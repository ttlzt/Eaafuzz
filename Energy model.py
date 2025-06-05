import os
import numpy as np
import random
from tensorflow.keras.models import load_model
from tensorflow.keras import backend as K
from tensorflow.keras.utils import get_custom_objects
import tensorflow as tf

# 定义 Focal Loss
def focal_loss(gamma=1.0, alpha=0.5):
    def focal_loss_fixed(y_true, y_pred):
        epsilon = tf.keras.backend.epsilon()
        y_pred = tf.clip_by_value(y_pred, epsilon, 1. - epsilon)
        y_true = tf.cast(y_true, tf.float32)
        cross_entropy = -y_true * tf.math.log(y_pred)
        loss = alpha * tf.pow((1 - y_pred), gamma) * cross_entropy
        return tf.reduce_mean(tf.reduce_sum(loss, axis=1))
    return focal_loss_fixed

# 注册 focal_loss 到 custom_objects 中
get_custom_objects().update({'focal_loss_fixed': focal_loss()})

# 加载模型
model = load_model('model.h5', custom_objects={'focal_loss_fixed': focal_loss()})

# 使用模型预测种子的字节概率
def predict_seed_probability(seed):
    input_data = np.array(list(seed), dtype=np.int64)

    if input_data.shape[0] < 7837:
        input_data = np.pad(input_data, (0, 7837 - input_data.shape[0]), 'constant')
    elif input_data.shape[0] > 7837:
        input_data = input_data[:7837]

    input_data = input_data.reshape(1, 7837)
    probabilities = model.predict(input_data)

    return probabilities

# 获取 'seeds' 文件夹中的所有文件
def get_random_files_from_seeds(folder_path, num_files=2):
    files = [f for f in os.listdir(folder_path) if os.path.isfile(os.path.join(folder_path, f))]
    if len(files) < num_files:
        raise ValueError("文件夹中的文件数量不足以进行选择。")
    selected_files = random.sample(files, num_files)
    return [os.path.join(folder_path, f) for f in selected_files]

# 拼接种子文件并使用模型预测拼接后的字节概率
def splice_seed(seeds_folder, idxx, gradient_info_file):
    # 随机选择两个文件
    f1, f2 = get_random_files_from_seeds(seeds_folder)
    print(f"随机选择的文件：{f1} 和 {f2}")

    # 读取文件内容
    with open(f1, 'rb') as file1:
        tmp1 = file1.read()
    with open(f2, 'rb') as file2:
        tmp2 = file2.read()

    # 判断文件长度，确保 tmp1 是较短的文件
    if len(tmp1) <= len(tmp2):
        head, tail = tmp1, tmp2
    else:
        head, tail = tmp2, tmp1

    f_diff = None
    l_diff = None

    # 查找首次不匹配的位置
    for i in range(min(len(head), len(tail))):
        if head[i] != tail[i]:
            f_diff = i
            break

    # 查找最后一次不匹配的位置
    for i in range(len(head) - 1, -1, -1):
        if head[i] != tail[i]:
            l_diff = i
            break

    # 确保首次和最后一次不匹配的位置有效
    if f_diff is not None and l_diff is not None and l_diff - f_diff > 1:
        splice_at = random.randint(f_diff + 1, l_diff - 1)
        head = list(head)
        tail = list(tail)
        head[:splice_at] = tail[:splice_at]

        result = bytes(head)

        save_path = os.path.join('./splice_seeds', f'tmp_{idxx}')
        with open(save_path, 'wb') as output_file:
            output_file.write(result)

        print(f'首次不匹配位置: {f_diff}, 最后一次不匹配位置: {l_diff}')
        print(f'保存拼接后的文件为: {save_path}')

        # 使用训练好的模型预测拼接后的种子
        probabilities = predict_seed_probability(result)

        # 将预测结果保存到 gradient_info_p 文件
        probabilities_str = ','.join(map(str, probabilities[0]))
        gradient_info_file.write(f"{save_path}|{probabilities_str}\n")

        print(f'预测概率保存为: gradient_info_p')

        return result, probabilities

    print("拼接不成功，尝试新的文件组合...")
    return None, None

# 创建保存预测概率的目录（如果不存在）
os.makedirs('./splice_seeds', exist_ok=True)

# 打开 gradient_info_p 文件，以写入模式
with open('gradient_info_p', 'w') as gradient_info_file:
    for i in range(1, 2001):  # 处理5000个种子
        seeds_folder = './neuzz_in'  # 种子文件夹路径
        result, probabilities = splice_seed(seeds_folder, i, gradient_info_file)

    print("所有种子的预测概率已保存。")

