import os
import glob
import random
import numpy as np
import tensorflow as tf
from tensorflow.keras import models, layers, regularizers
from tensorflow.keras.layers import LeakyReLU
from sklearn.model_selection import StratifiedKFold
from sklearn.model_selection import train_test_split
from tensorflow.keras.callbacks import ReduceLROnPlateau
from tensorflow.keras.callbacks import EarlyStopping


def read_file_as_ascii(filepath):
    with open(filepath, 'rb') as file:
        byte_data = file.read()
        ascii_values = list(byte_data)
    return ascii_values

def augment_data(ascii_values):
    # 添加噪声作为数据增强的示例
    noise = np.random.normal(0, 0.1, ascii_values.shape)  # 正态分布噪声
    augmented = np.clip(ascii_values + noise, 0, 1)  # 确保值在 [0, 1] 范围内
    return augmented



def process_directory(directory):
    all_ascii_values = []
    all_labels = []
    try:
        for filename in sorted(os.listdir(directory)):
            if filename.startswith("id:"):
                filepath = os.path.join(directory, filename)
                ascii_values = read_file_as_ascii(filepath)
                ascii_values = np.array(ascii_values) / 255  # 归一化
                all_ascii_values.append(ascii_values)
                
                # 数据增强
                augmented_ascii = augment_data(ascii_values)
                all_ascii_values.append(augmented_ascii)  # 添加增强的数据

                if '+cov' in filename:
                    pos_part = filename.split('pos:')[1].split(',')[0]
                    pos = int(pos_part)
                    label = [0] * len(ascii_values)
                    if pos < len(ascii_values):
                        label[pos] = 1
                    all_labels.append(label)
                    all_labels.append(label)  # 为增强的样本添加相应标签
                else:
                    all_labels.append([0] * len(ascii_values))
                    all_labels.append([0] * len(augmented_ascii))  # 为增强的样本添加标签
    except Exception as e:
        print(f"发生错误: {e}")
        
    return np.array(all_ascii_values, dtype=object), np.array(all_labels, dtype=object)


def focal_loss(gamma=2.0, alpha=0.25):
    def focal_loss_fixed(y_true, y_pred):
        epsilon = tf.keras.backend.epsilon()
        y_pred = tf.clip_by_value(y_pred, epsilon, 1. - epsilon)
        y_true = tf.cast(y_true, tf.float32)
        cross_entropy = -y_true * tf.math.log(y_pred)
        loss = alpha * tf.pow((1 - y_pred), gamma) * cross_entropy
        return tf.reduce_mean(tf.reduce_sum(loss, axis=1))
    return focal_loss_fixed

def build_sparse_coding_model(input_shape):
    l1_lambda = 1e-4
    l2_lambda = 1e-3
    model = models.Sequential([
        layers.Input(shape=(input_shape,)),
        layers.Dense(128, kernel_regularizer=regularizers.l2(l2_lambda),  
                     activity_regularizer=regularizers.l1(l1_lambda)),
        LeakyReLU(alpha=0.2),  # 使用 LeakyReLU 激活函数
        layers.Dropout(0.3),
        layers.Dense(64, kernel_regularizer=regularizers.l2(l2_lambda),  
                     activity_regularizer=regularizers.l1(l1_lambda)),
       # LeakyReLU(alpha=0.2),  # 使用 LeakyReLU 激活函数
        layers.Dense(input_shape, activation='sigmoid')
    ])
    model.compile(optimizer='adam', loss=focal_loss(gamma=1.0, alpha=0.5), metrics=['AUC'])
    return model




def main():
    directory = os.path.join(os.getcwd(), "Eaafuzz_in")
    X, y = process_directory(directory)

    # 找到最大长度并进行 padding
    max_length = max([len(x) for x in X])
    X = np.array([np.pad(x, (0, max_length - len(x)), 'constant') for x in X])
    y = np.array([np.pad(label, (0, max_length - len(label)), 'constant') for label in y])


    X = np.array(X, dtype=np.float32)
    y = np.array(y, dtype=np.float32)
    # 交叉验证配置
    kfold = StratifiedKFold(n_splits=5, shuffle=True, random_state=42)  # 5折交叉验证

    auc_scores = []  # 用于存储每一折的AUC得分
    for train_index, val_index in kfold.split(X, np.argmax(y, axis=1)):  # 使用最大标签作为分层依据
        X_train, X_val = X[train_index], X[val_index]
        y_train, y_val = y[train_index], y[val_index]


        # 训练稀疏编码模型
        model = build_sparse_coding_model(max_length)

        # 添加学习率衰减回调
        lr_scheduler = ReduceLROnPlateau(
            monitor='val_loss', 
            factor=0.1, 
            patience=10, 
            min_lr=1e-6, 
            verbose=1
        )

        # 训练模型
        history = model.fit(X_train, y_train, epochs=50, batch_size=16, validation_data=(X_val, y_val), callbacks=[lr_scheduler])

        # 计算验证集AUC
        auc_score = model.evaluate(X_val, y_val, verbose=0)[1]  # AUC在metrics中
        auc_scores.append(auc_score)

    # 输出每折的AUC得分和平均AUC
    print(f"每折的AUC得分：{auc_scores}")
    print(f"平均AUC得分：{np.mean(auc_scores)}")

    # 保存最后训练的模型
    model.save('model.h5')
    print("模型已保存为 model.h5")




if __name__ == "__main__":
    seed_list = []  # 在这里定义你的种子列表
    main()

